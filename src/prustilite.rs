use rustc_abi::Size;
use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{
        tcx::PlaceTy, BasicBlock, BinOp, Body, BorrowKind, Local, Operand, Place, ProjectionElem,
        Rvalue, Statement, Terminator, TerminatorKind, START_BLOCK,
    },
    ty::{List, Ty, TyCtxt, TyKind, TypeVisitor},
};
use rustc_span::Symbol;
use rustc_target::abi::VariantIdx;
use std::{
    collections::{HashMap, HashSet},
    fmt::Write as _,
    io::{Result, Write},
};

use crate::{
    aenealite::{
        diff_terms, for_all_vars, node_graph, Environ, LoanId, RegionCollector, SymResults,
        SymValue, SymValueI, WandTerm,
    },
    wto::{weak_topological_order, Component},
};

/// Emit viper methods for mir functions in a prusti style
///

pub fn encode_body<'tcx>(
    f: &mut dyn Write,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    res: &SymResults<'tcx>,
) -> Result<()> {
    let graph = node_graph(body);
    let wto = weak_topological_order(&graph, START_BLOCK);

    for c in wto {
        encode_component(f, tcx, body, &c, res)?;
    }
    writeln!(f, "");
    Ok(())
}

fn encode_component<'tcx>(
    f: &mut dyn Write,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    c: &Component<BasicBlock>,
    res: &SymResults<'tcx>,
) -> Result<()> {
    match c {
        Component::Vertex(bb) => encode_block(f, tcx, body, *bb, res),
        Component::Component(h, bdy) => encode_loop(f, tcx, body, *h, &bdy, res),
    }
}

// Since viper has unstructured control flow probs don't even need to do this,....
fn encode_loop<'tcx>(
    f: &mut dyn Write,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    head: BasicBlock,
    bdy: &[Component<BasicBlock>],
    res: &SymResults<'tcx>,
) -> Result<()> {
    encode_block(f, tcx, body, head, res)?;
    for bb in bdy {
        encode_component(f, tcx, body, bb, res)?;
    }
    Ok(())
}

fn encode_block<'tcx>(
    f: &mut dyn Write,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    res: &SymResults<'tcx>,
) -> Result<()> {
    writeln!(f, "label {bb:?};")?;
    let mut loc = bb.start_location();
    if let Some(pre_loop) = res.pre_loop_env.get(&loc) {
        invariants_between(f, body, pre_loop, res.envs.get(&loc).unwrap());
    }
    // println!("// {}", res.envs.get(&loc).unwrap_or_else(|| panic!("{loc:?}")));

    for s in &body[bb].statements {
        let prev_env = res.envs.get(&loc).unwrap();
        loc = loc.successor_within_block();
        let env = res.envs.get(&loc).unwrap();
        let mut out = Vec::new();
        let mut exhales = String::new();
        for_all_vars(prev_env, env, |l, pre, post| {
            let pty = PlaceTy::from_ty(body.local_decls[l].ty);
            match (pre, post) {
                (Some(pre), None) => {
                    if pre.has_loan() {
                        return;
                    }
                    let mut out = Vec::new();
                    // Try folding up `pre` again
                    fold_unfold(
                        tcx,
                        FoldUnfold::Unfold,
                        l,
                        pty,
                        Vec::new(),
                        pre.clone(),
                        SymValue::symbolic(pty.ty, 0),
                        &mut out,
                    );
                    for (comm, pl) in out {
                        writeln!(&mut exhales, " {comm}({pl:?});").unwrap();
                    }

                    // let mut out = Vec::new();
                    // val_to_place(tcx, l, pty, Vec::new(), &pre, &mut out);
                    // for pl in out {
                    writeln!(&mut exhales, "  exhale {l:?};").unwrap();
                    // }
                }
                (None, Some(_post)) => {
                    writeln!(f, "  var {l:?} : Ref := new(*);").unwrap();
                }
                (Some(pre), Some(post)) => {
                    // if pre == post {
                    //     eprintln!("comparing {pre} {post}");
                    // }
                    fold_unfold(tcx, FoldUnfold::Unfold, l, pty, Vec::new(), pre, post, &mut out);
                }
                _ => unreachable!(),
            }
        });

        // for f_or_f in out {
        //     println!("fold_or_unfold: {f_or_f:?}")
        // }

        encode_statement(f, tcx, body, s)?;
        write!(f, "{exhales}")?;
        // println!("// {}", res.envs.get(&loc).unwrap_or_else(|| panic!("{loc:?}")));
    }
    write!(f, "  ")?;
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
            write!(f, "  ")?;
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
    // if let Rvalue::Ref(_, BorrowKind::Mut { .. }, _) = asgn_2 {
    //     write!(f, ".deref")?;
    // }
    write!(f, ":=")?;
    match asgn_2 {
        Rvalue::Use(op) => encode_operand(f, tcx, body, op.clone()),
        Rvalue::UnaryOp(_, _) => todo!(),
        Rvalue::Discriminant(pl) => {
            encode_place(f, tcx, body, *pl)?;
            write!(f, ".discr")
        },
        Rvalue::Aggregate(_, _) => todo!(),
        Rvalue::Ref(_, BorrowKind::Mut { .. }, pl) => {
            // TODO need to add a deref to lhs
            let pl = if pl.projection.get(0) == Some(&ProjectionElem::Deref) {
                Place { local: pl.local, projection: tcx.mk_place_elems(&pl.projection[1..]) }
            } else {
                *pl
            };
            encode_place(f, tcx, body, pl)
        }
        Rvalue::Ref(_, _, _) => todo!("shared borrow"),
        Rvalue::Cast(_, _, _) => todo!(),
        Rvalue::BinaryOp(op, ops) | Rvalue::CheckedBinaryOp(op, ops) => {
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
        TerminatorKind::SwitchInt { discr, targets } => {
            write!(f, "var discr := ")?;
            encode_operand(f, tcx, body, discr.clone())?;
            writeln!(f, ";")?;
            use std::iter::*;
            let headers = once("if").chain(vec!["if else"; targets.iter().len() - 1]);
            for (hdr, (ix, tgt)) in headers.zip(targets.iter()) {
                writeln!(f, "  {hdr} (discr == {ix}) {{ goto {tgt:?}; }}")?;
            }
            writeln!(f, "  else {{ goto {:?}; }}", targets.otherwise())?;
            Ok(())
        }
        TerminatorKind::Return => writeln!(f, "return;"),
        TerminatorKind::Unreachable => todo!(),
        TerminatorKind::Drop { .. } => todo!(),
        TerminatorKind::Call { .. } => {
            todo!()
        }
        TerminatorKind::Assert { cond, target, .. } => {
            write!(f, "assert ")?;
            encode_operand(f, tcx, body, cond.clone())?;
            writeln!(f, ";")?;

            writeln!(f, "goto {target:?}")
        }
        TerminatorKind::FalseEdge { real_target, .. } => {
            writeln!(f, "goto {real_target:?}")
        }
        TerminatorKind::FalseUnwind { real_target, .. } => writeln!(f, "goto {real_target:?}"),
        _ => {
            todo!("unsupported terminator {bb:?}")
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum FoldUnfold {
    Fold,
    Unfold,
}

impl std::fmt::Display for FoldUnfold {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FoldUnfold::Fold => write!(f, "fold"),
            FoldUnfold::Unfold => write!(f, "unfold"),
        }
    }
}

fn fold_unfold<'tcx>(
    tcx: TyCtxt<'tcx>,
    mode: FoldUnfold,
    loc: Local,
    pty: PlaceTy<'tcx>,
    mut base: Vec<ProjectionElem<Local, Ty<'tcx>>>,
    pre: SymValue<'tcx>,
    post: SymValue<'tcx>,
    out: &mut Vec<(FoldUnfold, Place<'tcx>)>,
) {
    if pre == post {
        return;
    }
    match (&*pre, &*post) {
        (SymValueI::Borrow(_, _, p), SymValueI::Borrow(_, _, q)) => {
            base.push(ProjectionElem::Deref);
            let pty = pty.projection_ty(tcx, ProjectionElem::Deref);
            fold_unfold(tcx, mode, loc, pty, base, p.clone(), q.clone(), out);
        }
        (
            SymValueI::Constructor { id, nm, fields: ps, .. },
            SymValueI::Constructor { fields: qs, .. },
        ) => {
            let type_id = match tcx.def_kind(*id) {
                DefKind::Variant => tcx.parent(*id),
                _ => *id,
            };
            let adt = tcx.adt_def(type_id);

            let vix = adt.variant_index_with_id(*id);
            base.push(ProjectionElem::Downcast(Some(*nm), vix));
            let pty = pty.projection_ty(tcx, ProjectionElem::Downcast(Some(*nm), vix));

            for (ix, (p, q)) in ps.iter().zip(qs).enumerate() {
                if p == q {
                    continue;
                }
                let pty = pty;
                let ty = pty.field_ty(tcx, ix.into());
                let mut base = base.clone();
                base.push(ProjectionElem::Field(ix.into(), ty));
                let pty = pty.projection_ty(tcx, ProjectionElem::Field(ix.into(), ty));
                fold_unfold(tcx, mode, loc, pty, base, p.clone(), q.clone(), out);
            }
        }
        (SymValueI::Tuple(ps), SymValueI::Tuple(qs)) => {
            for (ix, (p, q)) in ps.iter().zip(qs).enumerate() {
                if p == q {
                    continue;
                }
                let mut base = base.clone();
                let ty = pty.field_ty(tcx, ix.into());
                base.push(ProjectionElem::Field(ix.into(), ty));
                let pty = pty.projection_ty(tcx, ProjectionElem::Field(ix.into(), ty));
                fold_unfold(tcx, mode, loc, pty, base, p.clone(), q.clone(), out);
            }
        }
        (SymValueI::Box(p), SymValueI::Box(q)) => {
            base.push(ProjectionElem::Deref);
            fold_unfold(tcx, mode, loc, pty, base, p.clone(), q.clone(), out);
        }
        (SymValueI::Symbolic(_, _), SymValueI::Symbolic(_, _)) => {}
        (SymValueI::Symbolic(ty, _), _) => {
            if let Some(val) = unfold(tcx, *ty, None) {
                out.push((mode, Place { local: loc, projection: tcx.mk_place_elems(&base[..]) }));

                // base.clone());
                fold_unfold(tcx, mode, loc, pty, base, val, post, out);
            }
            // unfold
            //
        }
        (_, SymValueI::Symbolic(ty, _)) => {
            if let Some(val) = unfold(tcx, *ty, None) {
                out.push((FoldUnfold::Fold, Place { local: loc, projection: tcx.mk_place_elems(&base[..]) }));

                // base.clone());
                fold_unfold(tcx, FoldUnfold::Fold, loc, pty, base, pre, val, out);
            }
        }
        // ?? is this justified??
        (_, SymValueI::Loan(_)) => {}
        _ => todo!("no fold / unfold needed / possible {pre} {post}"),
    }
}

/// Unfold a symbolic value and fully replace it everywhere in the symbolic environment.
fn unfold<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    variant: Option<VariantIdx>,
) -> Option<SymValue<'tcx>> {
    let new_val = match ty.kind() {
        TyKind::Bool => return None,
        TyKind::Char => return None,
        TyKind::Int(_) => return None,
        TyKind::Uint(_) => return None,
        TyKind::Float(_) => return None,
        TyKind::Str => return None,
        TyKind::Ref(_, ty, mutbl) => {
            SymValue::borrow(*mutbl, LoanId::Wild, SymValue::symbolic(*ty, 0))
        }

        TyKind::Tuple(fields) => {
            let fields = fields.iter().map(|ty| SymValue::symbolic(ty, 0)).collect();
            SymValue::tuple(fields)
        }

        TyKind::Adt(adt, substs) => {
            if adt.variants().len() > 1 && variant.is_none() {
                return None;
            }
            // assert!(adt.variants().len() == 1 || variant.is_some());

            let variant = &adt.variants()[variant.unwrap_or(0u32.into())];
            let fields: Vec<_> = variant
                .fields
                .iter()
                .map(|field| SymValue::symbolic(field.ty(tcx, substs), 0))
                .collect();
            let nm = variant.ident(tcx).name;

            if adt.is_box() {
                SymValue::box_(SymValue::symbolic(substs.type_at(0), 0))
            } else {
                SymValue::constructor(nm, variant.def_id, substs, fields)
            }
        }
        _ => tcx.dcx().fatal("unsupported type"),
    };

    Some(new_val)
}

/// Returns the initialized place in a value
fn val_to_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    local: Local,
    pty: PlaceTy<'tcx>,
    mut base: Vec<ProjectionElem<Local, Ty<'tcx>>>,
    pre: &SymValue<'tcx>,
    out: &mut Vec<Place<'tcx>>,
) {
    match &**pre {
        SymValueI::Symbolic(ty, _) => {
            assert_eq!(ty, &pty.ty);
            out.push(Place { local, projection: tcx.mk_place_elems(&base[..]) });
        }
        SymValueI::Loan(_) => out.push(Place { local, projection: tcx.mk_place_elems(&base[..]) }),
        SymValueI::Borrow(_, _, t) => {
            base.push(ProjectionElem::Deref);
            let pty = pty.projection_ty(tcx, ProjectionElem::Deref);
            val_to_place(tcx, local, pty, base, t, out);
        }
        SymValueI::Constructor { nm, id, fields, .. } => {
            let type_id = match tcx.def_kind(*id) {
                DefKind::Variant => tcx.parent(*id),
                _ => *id,
            };
            let adt = tcx.adt_def(type_id);

            let vix = adt.variant_index_with_id(*id);
            base.push(ProjectionElem::Downcast(Some(*nm), vix));
            let pty = pty.projection_ty(tcx, ProjectionElem::Downcast(Some(*nm), vix));

            fields.iter().enumerate().for_each(|(ix, f)| {
                let mut base = base.clone();
                let ty = pty.field_ty(tcx, ix.into());
                let pty = pty.projection_ty(tcx, ProjectionElem::Field(ix.into(), ty));
                base.push(ProjectionElem::Field(ix.into(), ty));
                val_to_place(tcx, local, pty, base, f, out);
            })
        }
        SymValueI::Tuple(ts) => ts.iter().enumerate().for_each(|(ix, f)| {
            let mut base = base.clone();
            let ty = pty.field_ty(tcx, ix.into());
            let pty = pty.projection_ty(tcx, ProjectionElem::Field(ix.into(), ty));
            base.push(ProjectionElem::Field(ix.into(), ty));
            val_to_place(tcx, local, pty, base, f, out);
        }),
        SymValueI::Box(s) => {
            base.push(ProjectionElem::Deref);
            val_to_place(tcx, local, pty, base, &*s, out)
        }
        SymValueI::Wild => out.push(Place { local, projection: tcx.mk_place_elems(&base[..]) }),
        SymValueI::Uninit => (),
    }
}

/// Calculate the loop invariant given a state immediately before a loop and a state immediately afterwards.
fn invariants_between<'tcx>(
    f: &mut dyn Write,
    // tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    pre: &Environ<'tcx>,
    post: &Environ<'tcx>,
) {
    let mut changed = HashMap::new();
    let mut affected_lifetimes: HashMap<_, HashSet<_>> = HashMap::new();
    for (k, v) in &pre.map {
        if post.get(*k) != Some(v.clone()) {
            changed.insert(k, v);

            let rust_ty = body.local_decls[*k].ty;
            let mut col = RegionCollector::default();
            col.visit_ty(rust_ty);

            for lft in col.regions {
                affected_lifetimes.entry(lft).or_default().insert(*k);
            }
        }
    }

    // eprintln!("needing magic wands {:?}", affected_lifetimes);

    for (_, vars) in affected_lifetimes {
        let mut out = Vec::new();
        for var in vars {

            // fold_unfold(tcx, FoldUnfold::Unfold, var, pty, Vec::new(), pre, post, &mut Vec::new());
            diff_terms(
                WandTerm::Var(var),
                &pre.get(var).unwrap(),
                &post.get(var).unwrap(),
                &mut out,
            );
        }
        let (pres, posts) = out.into_iter().unzip();

        let post = WandTerm::Conj(posts);
        let pre = WandTerm::Conj(pres);
        let wand = WandTerm::Wand(Box::new(post), Box::new(pre));
        writeln!(f, "invariant {wand};").unwrap();
    }
}
