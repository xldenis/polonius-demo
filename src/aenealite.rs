use std::{collections::HashMap, ops::Deref, rc::Rc};

use rustc_ast::Mutability;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{
        self, BasicBlock, BorrowKind, Local, LocalDecls, Operand, Place, ProjectionElem, Rvalue,
        Statement, Terminator,
    },
    ty::{GenericArgsRef, Ty, TyCtxt},
};
use rustc_target::abi::VariantIdx;
use rustc_type_ir::TyKind;

/// An experimental "lightweight" version of the Aeneas analysis which associates a symbolic value to each MIR place.

#[derive(Clone)]
enum SymValueI<'tcx> {
    Symbolic(Ty<'tcx>, usize),
    Loan(LoanId),
    Borrow(Mutability, LoanId, SymValue<'tcx>),
    Constructor { id: DefId, args: GenericArgsRef<'tcx>, fields: Vec<SymValue<'tcx>> },
    Tuple(Vec<SymValue<'tcx>>),
    Bot(Ty<'tcx>),
}

#[derive(Clone)]
struct SymValue<'tcx>(Rc<SymValueI<'tcx>>);

impl<'tcx> SymValue<'tcx> {
    fn constructor(id: DefId, args: GenericArgsRef<'tcx>, fields: Vec<Self>) -> Self {
        SymValue(Rc::new(SymValueI::Constructor { id, args, fields }))
    }

    fn borrow(m: Mutability, l: LoanId, v: Self) -> Self {
        SymValue(Rc::new(SymValueI::Borrow(m, l, v)))
    }

    fn loan(l: LoanId) -> Self {
        SymValue(Rc::new(SymValueI::Loan(l)))
    }

    fn tuple(fields: Vec<Self>) -> Self {
        SymValue(Rc::new(SymValueI::Tuple(fields)))
    }

    fn bot(ty: Ty<'tcx>) -> Self {
        SymValue(Rc::new(SymValueI::Bot(ty)))
    }

    fn symbolic(ty: Ty<'tcx>, id: usize) -> Self {
        SymValue(Rc::new(SymValueI::Symbolic(ty, id)))
    }
}

impl<'tcx> Deref for SymValue<'tcx> {
    type Target = SymValueI<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Copy)]
struct LoanId(usize);

struct Environ<'tcx> {
    map: HashMap<Local, SymValue<'tcx>>,
}

impl<'tcx> Environ<'tcx> {
    fn join(&mut self, other: &Self) {
        todo!("perform a pointwise join")
    }

    fn get(&self, l: Local) -> Option<SymValue<'tcx>> {
        self.map.get(&l).cloned()
    }
}

struct SymState<'tcx> {
    tcx: TyCtxt<'tcx>,
    env: Environ<'tcx>,
    fresh_loan: usize,
    fresh_sym: usize,
    locals: LocalDecls<'tcx>,
}

fn replace_sym<'tcx>(this: SymValue<'tcx>, ix: usize, val: SymValue<'tcx>) -> SymValue<'tcx> {
    match &*this {
        SymValueI::Symbolic(_, id) if *id == ix => val,
        SymValueI::Symbolic(_, _) => this,
        SymValueI::Loan(_) => this,
        SymValueI::Borrow(m, id, v) => SymValue::borrow(*m, *id, replace_sym(v.clone(), ix, val)),
        SymValueI::Constructor { id, args, fields } => {
            let fields = fields.iter().map(|f| replace_sym(f.clone(), ix, val.clone())).collect();
            SymValue::constructor(*id, args, fields)
        }
        SymValueI::Tuple(fields) => {
            let fields = fields.iter().map(|f| replace_sym(f.clone(), ix, val.clone())).collect();
            SymValue::tuple(fields)
        }
        SymValueI::Bot(_) => this,
    }
}

impl<'tcx> SymState<'tcx> {
    fn fresh_loan(&mut self) -> LoanId {
        let l = LoanId(self.fresh_loan);
        self.fresh_loan += 1;
        l
    }

    fn fresh_sym(&mut self, ty: Ty<'tcx>) -> SymValue<'tcx> {
        let id = self.fresh_sym;
        self.fresh_sym += 1;
        SymValue::symbolic(ty, id)
    }

    /// Unfold a symbolic value and fully replace it everywhere in the symbolic environment.
    fn unfold(
        &mut self,
        id: usize,
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
                SymValue::borrow(*mutbl, self.fresh_loan(), self.fresh_sym(*ty))
            }

            TyKind::Tuple(fields) => {
                let fields = fields.iter().map(|ty| self.fresh_sym(ty)).collect();
                SymValue::tuple(fields)
            }

            TyKind::Adt(adt, substs) => {
                assert!(adt.variants().len() == 1 || variant.is_some());

                let variant = &adt.variants()[variant.unwrap_or(0u32.into())];
                let fields = variant
                    .fields
                    .iter()
                    .map(|field| self.fresh_sym(field.ty(self.tcx, substs)))
                    .collect();

                SymValue::constructor(variant.def_id, substs, fields)
            }
            _ => self.tcx.dcx().fatal("unsupported type"),
        };

        // Replace the old value everywhere
        self.env
            .map
            .values_mut()
            .for_each(|val| *val = replace_sym(val.clone(), id, new_val.clone()));

        Some(new_val)
    }

    /// Produce an unfolded bottom for the given type
    fn unfold_bot(&mut self, ty: Ty<'tcx>, variant: Option<VariantIdx>) -> SymValue<'tcx> {
        let new_val = match ty.kind() {
            TyKind::Bool => return SymValue::bot(ty),
            TyKind::Char => return SymValue::bot(ty),
            TyKind::Int(_) => return SymValue::bot(ty),
            TyKind::Uint(_) => return SymValue::bot(ty),
            TyKind::Float(_) => return SymValue::bot(ty),
            TyKind::Str => return SymValue::bot(ty),
            TyKind::Ref(_, ty, mutbl) => {
                self.tcx.dcx().fatal("cannot unfold a bottom value of reference type")
            }

            TyKind::Tuple(fields) => {
                let fields = fields.iter().map(|ty| SymValue::bot(ty)).collect();
                SymValue::tuple(fields)
            }

            TyKind::Adt(adt, substs) => {
                assert!(adt.variants().len() == 1 || variant.is_some());

                let variant = &adt.variants()[variant.unwrap_or(0u32.into())];
                let fields = variant
                    .fields
                    .iter()
                    .map(|ty| SymValue::bot(ty.ty(self.tcx, substs)))
                    .collect();

                SymValue::constructor(variant.def_id, substs, fields)
            }
            _ => self.tcx.dcx().fatal("unsupported type"),
        };

        new_val
    }

    fn project_value(
        &mut self,
        v: SymValue<'tcx>,
        proj: ProjectionElem<Local, Ty<'tcx>>,
    ) -> SymValue<'tcx> {
        let v = if let SymValueI::Symbolic(ty, id) = &*v {
            let var = if let ProjectionElem::Downcast(_, idx) = proj { Some(idx) } else { None };
            self.unfold(*id, *ty, var).unwrap_or(v)
        } else {
            v
        };

        match proj {
            ProjectionElem::Deref => {
                if let SymValueI::Borrow(_, _, pointed) = &*v {
                    log::info!("dereferencing borrow value; suspicious");
                    return pointed.clone();
                } else {
                    self.tcx.dcx().fatal("dereferenced non-borrow value")
                }
            }
            ProjectionElem::Field(ix, _) => match &*v {
                SymValueI::Constructor { fields, .. } | SymValueI::Tuple(fields) => {
                    fields[ix.as_usize()].clone()
                }
                _ => self.tcx.dcx().fatal("field projection on non-aggregate type"),
            },
            ProjectionElem::Index(_) => self.tcx.dcx().fatal("index, unsupported projection"),
            ProjectionElem::ConstantIndex { .. } => {
                self.tcx.dcx().fatal("constantindex, unsupported projection")
            }
            ProjectionElem::Subslice { .. } => {
                self.tcx.dcx().fatal("subslice, unsupported projection")
            }
            ProjectionElem::Downcast(_, ix) => match &*v {
                SymValueI::Constructor { id, .. } => {
                    let type_id = match self.tcx.def_kind(*id) {
                        DefKind::Variant => self.tcx.parent(*id),
                        _ => *id,
                    };
                    let adt = self.tcx.adt_def(type_id);

                    assert_eq!(adt.variants()[ix].def_id, *id);
                    v
                }
                _ => self.tcx.dcx().fatal("downcast, unsupported projection"),
            },
            ProjectionElem::OpaqueCast(_) => {
                self.tcx.dcx().fatal("opaque cast, unsupported projection")
            }
            ProjectionElem::Subtype(_) => self.tcx.dcx().fatal("subtype, unsupported projection"),
        }
    }

    fn update_value(
        &mut self,
        mut lhs: SymValue<'tcx>,
        projs: &[ProjectionElem<Local, Ty<'tcx>>],
        rhs: SymValue<'tcx>,
    ) -> SymValue<'tcx> {
        if projs.is_empty() {
            return rhs;
        }

        if let SymValueI::Bot(ty) = &*lhs {
            let var =
                if let ProjectionElem::Downcast(_, idx) = projs[0] { Some(idx) } else { None };

            lhs = self.unfold_bot(*ty, var);
        }

        let proj = projs[0];
        match proj {
            ProjectionElem::Deref => {
                if let SymValueI::Borrow(m, l, pointed) = &*lhs {
                    return SymValue::borrow(
                        *m,
                        *l,
                        self.update_value(pointed.clone(), &projs[1..], rhs),
                    );
                } else {
                    self.tcx.dcx().fatal("dereferenced non-borrow value")
                }
            }
            ProjectionElem::Field(ix, _) => match &*lhs {
                SymValueI::Constructor { id, args, fields } => {
                    let updated =
                        self.update_value(fields[ix.as_usize()].clone(), &projs[1..], rhs);

                    let mut fields = fields.clone();

                    fields[ix.as_usize()] = updated;

                    SymValue::constructor(*id, args, fields)
                }
                SymValueI::Tuple(fields) => {
                    let updated =
                        self.update_value(fields[ix.as_usize()].clone(), &projs[1..], rhs);

                    let mut fields = fields.clone();

                    fields[ix.as_usize()] = updated;

                    SymValue::tuple(fields)
                }
                _ => self.tcx.dcx().fatal("writing to field of non-aggregate type"),
            },
            ProjectionElem::Downcast(_, ix) => match &*lhs {
                SymValueI::Constructor { id, .. } => {
                    let type_id = match self.tcx.def_kind(*id) {
                        DefKind::Variant => self.tcx.parent(*id),
                        _ => *id,
                    };
                    let adt = self.tcx.adt_def(type_id);

                    assert_eq!(adt.variants()[ix].def_id, *id);
                    self.update_value(lhs, &projs[1..], rhs)
                }
                _ => self.tcx.dcx().fatal("downcast, unsupported projection"),
            },

            ProjectionElem::Index(_) => self.tcx.dcx().fatal("Index, cannot write"),
            ProjectionElem::ConstantIndex { .. } => {
                self.tcx.dcx().fatal("ConstantIndex, cannot write")
            }
            ProjectionElem::Subslice { .. } => self.tcx.dcx().fatal("Subslice, cannot write"),
            ProjectionElem::OpaqueCast(_) => self.tcx.dcx().fatal("OpaqueCast, cannot write"),
            ProjectionElem::Subtype(_) => self.tcx.dcx().fatal("Subtype, cannot write"),
        }
    }

    fn write_place(&mut self, lhs: Place<'tcx>, rhs: SymValue<'tcx>) {
        let updated = self.update_value(
            self.env.get(lhs.local).unwrap_or(SymValue::bot(self.locals[lhs.local].ty)),
            lhs.projection,
            rhs,
        );
        self.env.map.insert(lhs.local, updated);
    }

    fn eval_place(&mut self, pl: Place<'tcx>) -> SymValue<'tcx> {
        let mut base_val = self.env.get(pl.local).expect("expected environment to contain value");

        for proj in pl.projection {
            base_val = self.project_value(base_val, proj);
        }

        base_val
    }

    fn eval_operand(&mut self, op: Operand<'tcx>) -> SymValue<'tcx> {
        match op {
            // TODO mark this as either move or not
            Operand::Copy(pl) => self.eval_place(pl),
            Operand::Move(pl) => self.eval_place(pl),
            Operand::Constant(c) => self.fresh_sym(c.ty()),
        }
    }

    fn eval_rvalue(&mut self, r: Rvalue<'tcx>) -> SymValue<'tcx> {
        match r {
            Rvalue::Use(op) => self.eval_operand(op),
            Rvalue::Ref(_, m, pl) => {
                let m = match m {
                    BorrowKind::Shared => Mutability::Not,
                    BorrowKind::Fake(_) => self.tcx.dcx().fatal("unsupported: fake borrow"),
                    BorrowKind::Mut { .. } => Mutability::Mut,
                };
                let loan = self.fresh_loan();
                self.write_place(pl, SymValue::loan(loan));

                let pl = self.eval_place(pl);
                SymValue::borrow(m, loan, pl)
            }
            Rvalue::Discriminant(_) => todo!(),
            Rvalue::Aggregate(_, _) => todo!(),
            Rvalue::Cast(_, _, _) => self.fresh_sym(r.ty(&self.locals, self.tcx)),
            Rvalue::BinaryOp(_, _) => self.fresh_sym(r.ty(&self.locals, self.tcx)),
            Rvalue::CheckedBinaryOp(_, _) => self.fresh_sym(r.ty(&self.locals, self.tcx)),
            Rvalue::NullaryOp(_, _) => self.fresh_sym(r.ty(&self.locals, self.tcx)),
            Rvalue::UnaryOp(_, _) => self.fresh_sym(r.ty(&self.locals, self.tcx)),
            Rvalue::ShallowInitBox(_, _) => self.tcx.dcx().fatal("shallow init box"),
            Rvalue::CopyForDeref(_) => self.tcx.dcx().fatal("copy for deref"),
            Rvalue::Repeat(_, _) => self.tcx.dcx().fatal(" repeat"),
            Rvalue::ThreadLocalRef(_) => self.tcx.dcx().fatal(" thread local ref"),
            Rvalue::AddressOf(_, _) => self.tcx.dcx().fatal(" address of"),
            Rvalue::Len(_) => self.tcx.dcx().fatal("len"),
        }
    }

    fn eval_statement(&mut self, stmt: Statement<'tcx>) {
        match stmt.kind {
            mir::StatementKind::Assign(asgn) => {
                let rhs = self.eval_rvalue(asgn.1);
                self.write_place(asgn.0, rhs)
            }
            mir::StatementKind::FakeRead(_) => {
                log::info!("fake read; ignoring");
            }
            mir::StatementKind::SetDiscriminant { .. } => {
                self.tcx.dcx().fatal("set discriminant; unsupported")
            }
            mir::StatementKind::Deinit(_) => todo!(),
            mir::StatementKind::StorageLive(_) => log::info!("storage live; ignoring"),
            mir::StatementKind::StorageDead(_) => log::info!("storage dead; ignoring"),
            mir::StatementKind::Retag(_, _) => log::info!("retag; ignoring"),
            mir::StatementKind::PlaceMention(_) => log::info!("place mention; ignoring"),
            mir::StatementKind::AscribeUserType(_, _) => log::info!("ascribe; ignoring"),
            mir::StatementKind::Coverage(_) => log::info!("coverage; ignoring"),
            mir::StatementKind::Intrinsic(_) => todo!(),
            mir::StatementKind::ConstEvalCounter => log::info!("const eval counter; ignoring"),
            mir::StatementKind::Nop => log::info!("nop; ignoring"),
        }
    }

    fn eval_terminator(&mut self, term: Terminator<'tcx>) -> Vec<BasicBlock> {
        match term.kind {
            mir::TerminatorKind::Goto { target } => vec![target],
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let _ = self.eval_operand(discr);

                targets.all_targets().to_vec()
            }
            mir::TerminatorKind::Return => vec![],
            mir::TerminatorKind::Unreachable => vec![],
            mir::TerminatorKind::Drop { target, .. } => {
                log::info!("ignoring drop terminator...");
                vec![target]
            }
            mir::TerminatorKind::Call { func, args, destination, target, .. } => {
                let _ = self.eval_operand(func);

                let _ = args.iter().for_each(|op| {
                    self.eval_operand(op.node.clone());
                });

                let ret_val = self.fresh_sym(destination.ty(&self.locals, self.tcx).ty);
                self.write_place(destination, ret_val);

                vec![target.unwrap()]
            }
            mir::TerminatorKind::FalseEdge { .. } => self.tcx.dcx().fatal("unhandled terminator"),
            mir::TerminatorKind::Assert { .. } => self.tcx.dcx().fatal("unhandled terminator"),
            mir::TerminatorKind::Yield { .. } => self.tcx.dcx().fatal("unhandled terminator"),
            mir::TerminatorKind::UnwindResume => self.tcx.dcx().fatal("unhandled terminator"),
            mir::TerminatorKind::UnwindTerminate(_) => self.tcx.dcx().fatal("unhandled terminator"),
            mir::TerminatorKind::CoroutineDrop => self.tcx.dcx().fatal("unhandled terminator"),
            mir::TerminatorKind::FalseUnwind { .. } => self.tcx.dcx().fatal("unhandled terminator"),
            mir::TerminatorKind::InlineAsm { .. } => self.tcx.dcx().fatal("unhandled terminator"),
        }
    }
}
