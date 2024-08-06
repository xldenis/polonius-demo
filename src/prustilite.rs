use rustc_abi::Size;
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, BorrowKind, Operand, Place, ProjectionElem, Rvalue, Statement,
        Terminator, TerminatorKind, START_BLOCK,
    },
    ty::TyCtxt,
};
use std::io::{Result, Write};

use crate::{
    aenealite::node_graph,
    wto::{weak_topological_order, Component},
};

/// Emit viper methods for mir functions in a prusti style
///

pub fn encode_body<'tcx>(f: &mut dyn Write, tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Result<()> {
    let graph = node_graph(body);
    let wto = weak_topological_order(&graph, START_BLOCK);

    for c in wto {
        encode_component(f, tcx, body, &c)?;
    }
    Ok(())
}

fn encode_component<'tcx>(
    f: &mut dyn Write,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    c: &Component<BasicBlock>,
) -> Result<()> {
    match c {
        Component::Vertex(bb) => encode_block(f, tcx, body, *bb),
        Component::Component(h, bdy) => encode_loop(f, tcx, body, *h, &bdy),
    }
}

// Since viper has unstructured control flow probs don't even need to do this,....
fn encode_loop<'tcx>(
    f: &mut dyn Write,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    head: BasicBlock,
    bdy: &[Component<BasicBlock>],
) -> Result<()> {
    encode_block(f, tcx, body, head)?;
    for bb in bdy {
        encode_component(f, tcx, body, bb)?;
    }
    Ok(())
}

fn encode_block<'tcx>(
    f: &mut dyn Write,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
) -> Result<()> {
    writeln!(f, "label {bb:?};")?;
    for s in &body[bb].statements {
        encode_statement(f, tcx, body, s)?;
    }
    encode_terminator(f, tcx, body, &body[bb].terminator())
}

fn encode_statement<'tcx>(
    f: &mut dyn Write,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    s: &Statement<'tcx>,
) -> Result<()> {
    match &s.kind {
        rustc_middle::mir::StatementKind::Assign(asgn) => {
            encode_assign(f, tcx, body, &asgn.0, &asgn.1)?;
        }
        rustc_middle::mir::StatementKind::SetDiscriminant { place, variant_index } => {
            // println!("Skipping SetDiscriminant")
        }

        rustc_middle::mir::StatementKind::Deinit(_) => {
            // println!("Skipping Deinit...")
        }
        rustc_middle::mir::StatementKind::StorageLive(_) => {
            // println!("Skipping StorageLive...")
        }
        rustc_middle::mir::StatementKind::StorageDead(_) => {
            // println!("Skipping StorageDead...")
        }
        rustc_middle::mir::StatementKind::Retag(_, _) => {
            // println!("Skipping Retag...")
        }
        rustc_middle::mir::StatementKind::PlaceMention(_) => {
            // println!("Skipping PlaceMention...")
        }
        rustc_middle::mir::StatementKind::AscribeUserType(_, _) => {
            // println!("Skipping AscribeUserType...")
        }
        rustc_middle::mir::StatementKind::FakeRead(_) => {
            // println!("Skipping FakeRead...")
        }
        rustc_middle::mir::StatementKind::Coverage(_) => {
            // println!("Skipping Coverage...")
        }
        rustc_middle::mir::StatementKind::Intrinsic(_) => {
            // println!("Skipping Intrinsic...")
        }
        rustc_middle::mir::StatementKind::ConstEvalCounter => {
            // println!("Skipping ConstEvalCounter...")
        }
        rustc_middle::mir::StatementKind::Nop => {
            // println!("Skipping Nop...")
        }
    };
    Ok(())
}

fn encode_assign<'tcx>(
    f: &mut dyn Write,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    asgn_1: &Place<'tcx>,
    asgn_2: &Rvalue<'tcx>,
) -> Result<()> {
    encode_place(f, tcx, body, *asgn_1)?;
    if let Rvalue::Ref(_, BorrowKind::Mut { .. }, _) = asgn_2 {
        write!(f, ".deref")?;
    }
    write!(f, ":=")?;
    match asgn_2 {
        Rvalue::Use(op) => encode_operand(f, tcx, body, op.clone()),
        Rvalue::UnaryOp(_, _) => todo!(),
        Rvalue::Discriminant(_) => todo!(),
        Rvalue::Aggregate(_, _) => todo!(),
        Rvalue::Ref(_, BorrowKind::Mut { .. }, pl) => {
            // TODO need to add a deref to lhs
            encode_place(f, tcx, body, *pl)
        }
        Rvalue::Ref(_, _, _) => todo!("shared borrow"),
        Rvalue::Cast(_, _, _) => todo!(),
        Rvalue::BinaryOp(_, _) => todo!(),
        Rvalue::CheckedBinaryOp(op, ops) => {
            encode_operand(f, tcx, body, ops.0.clone())?;
            encode_binop(f, *op)?;
            encode_operand(f, tcx, body, ops.1.clone())
        }
        _ => todo!("unsupported rvalue"),
    }?;
    write!(f, ";\n")
}

fn encode_operand<'tcx>(
    f: &mut dyn Write,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    op: Operand<'tcx>,
) -> Result<()> {
    match op {
        Operand::Move(pl) | Operand::Copy(pl) => encode_place(f, tcx, body, pl),
        Operand::Constant(c) => {
            if c.ty().is_bool() {
                let bool = c.const_.try_to_bool().expect("could not get bool");
                write!(f, "{bool}")
            } else {
                if c.ty().is_unit() {
                    write!(f, "()")?;
                    return Ok(());
                }
                let bits = c
                    .const_
                    .try_to_bits(c.ty().primitive_size(tcx))
                    .expect(&format!("could not convert bits: {:?}", c.ty()));

                write!(f, "{bits}")
            }
        }
    }
}

// Do I need a different encoding on left and right sides? I don't think so...
fn encode_place<'tcx>(
    f: &mut dyn Write,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    asgn_1: Place<'tcx>,
) -> Result<()> {
    write!(f, "{:?}", asgn_1.local)?;
    for elem in asgn_1.projection {
        match elem {
            ProjectionElem::Deref => write!(f, ".deref")?,
            ProjectionElem::Field(ix, _) => {
                write!(f, ".field{}", ix.as_usize())?;
            }
            ProjectionElem::Index(_) => todo!("index"),
            ProjectionElem::ConstantIndex { .. } => todo!("constantindex"),
            ProjectionElem::Subslice { .. } => todo!("subslice"),
            ProjectionElem::Downcast(s, ix) => {
                if let Some(s) = s {
                    write!(f, ".{s}")?;
                } else {
                    write!(f, ".variant{}", ix.as_usize())?;
                }
            }
            ProjectionElem::OpaqueCast(_) => todo!("opaque"),
            ProjectionElem::Subtype(_) => todo!("subtype"),
        };
    }
    Ok(())
}

fn encode_binop(f: &mut dyn Write, op: BinOp) -> Result<()> {
    match op {
        BinOp::Add => write!(f, "+"),
        BinOp::AddUnchecked => write!(f, "+"), // Same symbol, but unchecked
        BinOp::Sub => write!(f, "-"),
        BinOp::SubUnchecked => write!(f, "-"), // Same symbol, but unchecked
        BinOp::Mul => write!(f, "*"),
        BinOp::MulUnchecked => write!(f, "*"), // Same symbol, but unchecked
        BinOp::Div => write!(f, "/"),
        BinOp::Rem => write!(f, "%"),
        BinOp::BitXor => write!(f, "^"),
        BinOp::BitAnd => write!(f, "&"),
        BinOp::BitOr => write!(f, "|"),
        BinOp::Shl => write!(f, "<<"),
        BinOp::ShlUnchecked => write!(f, "<<"), // Same symbol, but unchecked
        BinOp::Shr => write!(f, ">>"),
        BinOp::ShrUnchecked => write!(f, ">>"), // Same symbol, but unchecked
        BinOp::Eq => write!(f, "=="),
        BinOp::Lt => write!(f, "<"),
        BinOp::Le => write!(f, "<="),
        BinOp::Ne => write!(f, "!="),
        BinOp::Ge => write!(f, ">="),
        BinOp::Gt => write!(f, ">"),
        BinOp::Cmp => write!(f, "<=>"),
        BinOp::Offset => write!(f, "offset"), // No standard symbol, using the name
    }
}

fn encode_terminator<'tcx>(
    f: &mut dyn Write,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: &Terminator<'tcx>,
) -> Result<()> {
    match &bb.kind {
        TerminatorKind::Goto { target } => writeln!(f, "goto {target:?};"),
        TerminatorKind::SwitchInt { discr, targets } => todo!(),
        TerminatorKind::Return => writeln!(f, "return;"),
        TerminatorKind::Unreachable => todo!(),
        TerminatorKind::Drop { place, target, unwind, replace } => todo!(),
        TerminatorKind::Call { func, args, destination, target, unwind, call_source, fn_span } => {
            todo!()
        }
        TerminatorKind::Assert { cond, expected, msg, target, unwind } => {
            write!(f, "assert ")?;
            encode_operand(f, tcx, body, cond.clone())?;
            writeln!(f, ";")?;

            writeln!(f, "goto {target:?}")
        }
        TerminatorKind::FalseEdge { real_target, imaginary_target } => {
            writeln!(f, "goto {real_target:?}")
        }
        TerminatorKind::FalseUnwind { real_target, .. } => writeln!(f, "goto {real_target:?}"),
        _ => {
            todo!("unsupported terminator {bb:?}")
        }
    }
}
