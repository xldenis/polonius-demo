use std::{collections::HashMap, rc::Rc};

use rustc_ast::Mutability;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, BorrowKind, Place, Terminator};
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

type SymValue<'tcx> = Rc<SymValueI<'tcx>>;

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
        SymValueI::Borrow(m, id, v) => {
          Rc::new(SymValueI::Borrow(*m, *id, replace_sym(*v, ix, val)))
        },
        SymValueI::Constructor { id, args, fields } => todo!(),
        SymValueI::Tuple(_) => todo!(),
        SymValueI::Bot => todo!(),
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
        Rc::new(SymValueI::Symbolic(ty, id))
    }

    /// Unfold a symbolic value and fully replace it everywhere in the symbolic environment.
    fn unfold(&mut self, id: usize, ty: Ty<'tcx>, variant: Option<VariantIdx>) {
        let new_val = match ty.kind() {
            TyKind::Bool => return,
            TyKind::Char => return,
            TyKind::Int(_) => return,
            TyKind::Uint(_) => return,
            TyKind::Float(_) => return,
            TyKind::Str => return,
            TyKind::Ref(_, ty, mutbl) => Rc::new(SymValueI::Borrow(
                *mutbl,
                self.fresh_loan(),
                self.fresh_sym(*ty),
            )),
            TyKind::Tuple(fields) => {
                let fields = fields.iter().map(|ty| self.fresh_sym(ty)).collect();
                Rc::new(SymValueI::Tuple(fields))
            }

            TyKind::Adt(adt, substs) => {
                assert!(adt.variants().len() == 1 || variant.is_some());

                let variant = &adt.variants()[variant.unwrap_or(0u32.into())];
                let fields = variant
                    .fields
                    .iter()
                    .map(|field| self.fresh_sym(field.ty(self.tcx, substs)))
                    .collect();

                Rc::new(SymValueI::Constructor {
                    id: variant.def_id,
                    args: substs,
                    fields,
                })
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
    }

    fn project_value(
        &mut self,
        v: SymValue<'tcx>,
        proj: ProjectionElem<Local, Ty<'tcx>>,
    ) -> SymValue<'tcx> {
        if let SymValueI::Symbolic(ty, id) = &*v {
            let var = if let ProjectionElem::Downcast(_, idx) = proj {
                Some(idx)
            } else {
                None
            };
            self.unfold(*id, *ty, var);
        }
        match proj {
            ProjectionElem::Deref => todo!(),
            ProjectionElem::Field(_, _) => todo!(),
            ProjectionElem::Index(_) => todo!(),
            ProjectionElem::ConstantIndex {
                offset,
                min_length,
                from_end,
            } => todo!(),
            ProjectionElem::Subslice { from, to, from_end } => todo!(),
            ProjectionElem::Downcast(_, _) => todo!(),
            ProjectionElem::OpaqueCast(_) => todo!(),
            ProjectionElem::Subtype(_) => todo!(),
        }
    }

    fn eval_place(&mut self, pl: Place<'tcx>) -> SymValue<'tcx> {
        let mut base_val = self
            .env
            .get(pl.local)
            .expect("expected environment to contain value");

        for proj in pl.projection {
            base_val = base_val.project(proj);
        }

        base_val
    }

    fn eval_operand(&mut self, op: Operand<'tcx>) -> SymValue<'tcx> {
        todo!()
    }

    fn eval_statement(&mut self, stmt: Statement<'tcx>) {
        todo!()
    }

    fn eval_terminator(&mut self, term: Terminator<'tcx>) -> Vec<BasicBlock> {
        todo!()
    }
}
