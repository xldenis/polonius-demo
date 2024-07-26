use std::ops::Deref;
use std::{collections::HashMap, rc::Rc};

use rustc_ast::Mutability;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, BorrowKind, Place, Rvalue, Terminator};
use rustc_middle::ty::TyCtxt;
use rustc_middle::{
    mir::{self, Local, Operand, ProjectionElem, Statement},
    ty::{GenericArgsRef, Ty},
};
use rustc_target::abi::VariantIdx;
use rustc_type_ir::TyKind;

/// An experimental "lightweight" version of the Aeneas analysis which associates a symbolic value to each MIR place.

#[derive(Clone)]
enum SymValueI<'tcx> {
    Symbolic(Ty<'tcx>, usize),
    Loan(LoanId),
    Borrow(Mutability, LoanId, SymValue<'tcx>),
    Constructor {
        id: DefId,
        args: GenericArgsRef<'tcx>,
        fields: Vec<SymValue<'tcx>>,
    },
    Tuple(Vec<SymValue<'tcx>>),
    Bot,
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

    fn bot() -> Self {
        SymValue(Rc::new(SymValueI::Bot))
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
}

fn replace_sym<'tcx>(this: SymValue<'tcx>, ix: usize, val: SymValue<'tcx>) -> SymValue<'tcx> {
    match &*this {
        SymValueI::Symbolic(_, id) if *id == ix => val,
        SymValueI::Symbolic(_, _) => this,
        SymValueI::Loan(_) => this,
        SymValueI::Borrow(m, id, v) => SymValue::borrow(*m, *id, replace_sym(v.clone(), ix, val)),
        SymValueI::Constructor { id, args, fields } => {
            let fields = fields
                .iter()
                .map(|f| replace_sym(f.clone(), ix, val.clone()))
                .collect();
            SymValue::constructor(*id, args, fields)
        }
        SymValueI::Tuple(fields) => {
            let fields = fields
                .iter()
                .map(|f| replace_sym(f.clone(), ix, val.clone()))
                .collect();
            SymValue::tuple(fields)
        }
        SymValueI::Bot => this,
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
            TyKind::Slice(_) => self.tcx.dcx().fatal("not yet supported: slice"),
            TyKind::Foreign(_) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::Array(_, _) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::RawPtr(_, _) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::FnDef(_, _) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::FnPtr(_) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::Never => self.tcx.dcx().fatal("unsupported type"),
            TyKind::Dynamic(_, _, _) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::Closure(_, _) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::CoroutineClosure(_, _) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::Coroutine(_, _) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::CoroutineWitness(_, _) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::Pat(_, _) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::Alias(_, _) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::Param(_) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::Bound(_, _) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::Placeholder(_) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::Infer(_) => self.tcx.dcx().fatal("unsupported type"),
            TyKind::Error(_) => self.tcx.dcx().fatal("unsupported type"),
        };

        // Replace the old value everywhere
        self.env
            .map
            .values_mut()
            .for_each(|val| *val = replace_sym(val.clone(), id, new_val.clone()));

        Some(new_val)
    }

    fn project_value(
        &mut self,
        v: SymValue<'tcx>,
        proj: ProjectionElem<Local, Ty<'tcx>>,
    ) -> SymValue<'tcx> {
        let v = if let SymValueI::Symbolic(ty, id) = &*v {
            let var = if let ProjectionElem::Downcast(_, idx) = proj {
                Some(idx)
            } else {
                None
            };
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
                _ => self
                    .tcx
                    .dcx()
                    .fatal("field projection on non-aggregate type"),
            },
            ProjectionElem::Index(_) => self.tcx.dcx().fatal("index, unsupported projection"),
            ProjectionElem::ConstantIndex { .. } => self
                .tcx
                .dcx()
                .fatal("constantindex, unsupported projection"),
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

    fn eval_place(&mut self, pl: Place<'tcx>) -> SymValue<'tcx> {
        let mut base_val = self
            .env
            .get(pl.local)
            .expect("expected environment to contain value");

        for proj in pl.projection {
            base_val = self.project_value(base_val, proj);
        }

        base_val
    }

    fn eval_operand(&mut self, op: Operand<'tcx>) -> SymValue<'tcx> {
        match op {
            Operand::Copy(pl) => self.eval_place(pl),
            Operand::Move(pl) => self.eval_place(pl),
            Operand::Constant(c) => self.fresh_sym(c.ty()),
        }
    }

    fn eval_rvalue(&mut self, r: Rvalue<'tcx>) -> SymValue<'tcx> {
        todo!()
    }

    fn eval_assign(&mut self, lhs: Place<'tcx>, rhs: SymValue<'tcx>) {
        todo!()
    }

    fn eval_statement(&mut self, stmt: Statement<'tcx>) {
        match stmt.kind {
            mir::StatementKind::Assign(asgn) => {
                let rhs = self.eval_rvalue(asgn.1);
                self.eval_assign(asgn.0, rhs)
            }
            mir::StatementKind::FakeRead(_) => {
                log::info!("fake read; ignoring");
            }
            mir::StatementKind::SetDiscriminant {
               ..
            } => self.tcx.dcx().fatal("set discriminant; unsupported"),
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
        todo!()
    }
}
