use std::{
    cell::{Cell, RefCell},
    collections::{HashMap, HashSet},
    fmt::{Display, Formatter},
    ops::Deref,
    rc::Rc,
};

use petgraph::graphmap::DiGraphMap;
use rustc_ast::Mutability;
use rustc_borrowck::consumers::BodyWithBorrowckFacts;
use rustc_data_structures::graph::Successors;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{
        self, tcx::PlaceTy, BasicBlock, Body, BorrowKind, Local, LocalDecls, Location, Operand, Place, ProjectionElem, Rvalue, Statement, Terminator, START_BLOCK
    },
    ty::{GenericArgsRef, List, Region, RegionVid, Ty, TyCtxt, TypeVisitor},
};
use rustc_span::{Span, Symbol};
use rustc_target::abi::{FieldIdx, VariantIdx};
use rustc_type_ir::TyKind;

use std::hash::Hash;

use crate::{
    wto::{weak_topological_order, Component},
    MIR_BODIES,
};

fn merge_hashmaps<K, V, F>(map1: &mut HashMap<K, V>, map2: &HashMap<K, V>, mut merge_fn: F)
where
    K: Eq + Hash + Clone,
    V: Clone,
    F: FnMut(Option<&V>, Option<&V>) -> V,
{
    // Collect all unique keys from both maps
    let all_keys: Vec<K> = map1
        .keys()
        .chain(map2.keys())
        .cloned()
        .collect::<std::collections::HashSet<_>>()
        .into_iter()
        .collect();

    // Apply merge function for each key
    for key in all_keys {
        let value1 = map1.get(&key);
        let value2 = map2.get(&key);
        let merged_value = merge_fn(value1, value2);
        map1.insert(key, merged_value);
    }
}

/// An experimental "lightweight" version of the Aeneas analysis which associates a symbolic value to each MIR place.

#[derive(Clone, Debug, PartialEq)]
enum SymValueI<'tcx> {
    Symbolic(Ty<'tcx>, usize),
    Loan(LoanId),
    Borrow(Mutability, LoanId, SymValue<'tcx>),
    Constructor {
        nm: Symbol,
        id: DefId,
        args: GenericArgsRef<'tcx>,
        fields: Vec<SymValue<'tcx>>,
    },
    Tuple(Vec<SymValue<'tcx>>),
    /// We distinguish Box here since it has special behaviors
    Box(SymValue<'tcx>),
    /// Top in the lattice
    Wild,
    /// Also top? in the lattice?
    Uninit,
}

impl<'tcx> SymValue<'tcx> {
    /// Returns true of this is anything other than bot, symbolic or a loan identifer
    fn is_complex(&self) -> bool {
        match &**self {
            SymValueI::Symbolic(_, _) => false,
            SymValueI::Loan(_) => false,
            SymValueI::Uninit => false,
            SymValueI::Wild => false,
            _ => true,
        }
    }
}
impl Display for LoanId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LoanId::Id(id) => write!(f, "{id}"),
            LoanId::Wild => write!(f, "_"),
        }
    }
}

impl Display for SymValue<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &**self {
            SymValueI::Symbolic(_, id) => write!(f, "σ({id})"),
            SymValueI::Loan(l) => write!(f, "loan({})", l),
            SymValueI::Borrow(m, l, v) => {
                let borrow = match m {
                    Mutability::Not => "&",
                    Mutability::Mut => "&mut",
                };
                write!(f, "{} loan({}) ", borrow, l)?;
                if v.is_complex() {
                    write!(f, "({v})")
                } else {
                    write!(f, "{v}")
                }
            }
            SymValueI::Constructor { nm, fields, .. } => {
                write!(f, "{nm} {{")?;

                for field in fields {
                    if field.is_complex() {
                        write!(f, "({field}), ")?;
                    } else {
                        write!(f, "{field}, ")?;
                    }
                }
                write!(f, "}}")
            }
            SymValueI::Box(b) => {
                write!(f, "box ")?;
                if b.is_complex() {
                    write!(f, "({b})")
                } else {
                    write!(f, "{b}")
                }
            }
            SymValueI::Tuple(fields) => {
                write!(f, "(")?;
                for field in fields {
                    if field.is_complex() {
                        write!(f, "({field}), ")?;
                    } else {
                        write!(f, "{field}, ")?;
                    }
                }
                write!(f, ")")
            }
            SymValueI::Wild => write!(f, "_"),
            SymValueI::Uninit => write!(f, "⊥"),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct SymValue<'tcx>(Rc<SymValueI<'tcx>>);

impl<'tcx> SymValue<'tcx> {
    fn constructor(nm: Symbol, id: DefId, args: GenericArgsRef<'tcx>, fields: Vec<Self>) -> Self {
        SymValue(Rc::new(SymValueI::Constructor { nm, id, args, fields }))
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
        SymValue(Rc::new(SymValueI::Uninit))
    }

    fn wild() -> Self {
        SymValue(Rc::new(SymValueI::Wild))
    }

    fn box_(inner: Self) -> Self {
        SymValue(Rc::new(SymValueI::Box(inner)))
    }

    fn symbolic(ty: Ty<'tcx>, id: usize) -> Self {
        SymValue(Rc::new(SymValueI::Symbolic(ty, id)))
    }

    fn is_uninit(&self) -> bool {
        matches!(&*self.0, SymValueI::Uninit)
    }

    fn fold(&self) -> Self {
        match &*self.0 {
            SymValueI::Symbolic(_, _) => self.clone(),
            SymValueI::Loan(_) => self.clone(),
            SymValueI::Borrow(_, _, _) => self.clone(),
            SymValueI::Constructor { nm, id, args, fields } => {
                let fields = fields.iter().map(|f| f.fold()).collect();

                SymValue::constructor(*nm, *id, args, fields)
            }
            SymValueI::Tuple(flds) => {
                let flds: Vec<_> = flds.iter().map(|f| f.fold()).collect();
                if flds.iter().all(SymValue::is_uninit) {
                    SymValue::bot()
                } else {
                    SymValue::tuple(flds)
                }
            }
            SymValueI::Box(b) => SymValue::box_(b.fold()),
            SymValueI::Wild => self.clone(),
            SymValueI::Uninit => self.clone(),
        }
    }

    /// Returns true if there is a substitution renaming loans and symbolic values between the two tools
    fn weak_unification(&self, rhs: &Self, subst: &mut Substitution) -> bool {
        match (&*self.0, &*rhs.0) {
            (SymValueI::Symbolic(_, u), SymValueI::Symbolic(_, v)) => {
                subst.syms.insert(*u, *v);
                true
            }
            (SymValueI::Loan(l), SymValueI::Loan(k)) => {
                subst.loans.insert(*l, *k);
                true
            }
            (SymValueI::Borrow(_, l, f), SymValueI::Borrow(_, k, g)) => {
                subst.loans.insert(*l, *k);
                // unify l and k
                f.weak_unification(g, subst)
            }
            (
                SymValueI::Constructor { fields: fs, .. },
                SymValueI::Constructor { fields: gs, .. },
            ) => fs.iter().zip(gs).all(|(f, g)| f.weak_unification(g, subst)),
            (SymValueI::Tuple(fs), SymValueI::Tuple(gs)) => {
                fs.iter().zip(gs).all(|(f, g)| f.weak_unification(g, subst))
            }
            (SymValueI::Box(f), SymValueI::Box(g)) => f.weak_unification(g, subst),
            (SymValueI::Wild, SymValueI::Wild) => true,
            (SymValueI::Uninit, SymValueI::Uninit) => true,
            _ => false,
        }
    }
}

impl<'tcx> Deref for SymValue<'tcx> {
    type Target = SymValueI<'tcx>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Hash, Eq)]
enum LoanId {
    Id(usize),
    Wild,
}

#[derive(Default)]
struct Substitution {
    loans: HashMap<LoanId, LoanId>,
    syms: HashMap<usize, usize>,
}

#[derive(Clone, PartialEq)]
struct Environ<'tcx> {
    map: HashMap<Local, SymValue<'tcx>>,
}

impl<'tcx> Environ<'tcx> {
    fn get(&self, l: Local) -> Option<SymValue<'tcx>> {
        self.map.get(&l).cloned()
    }

    /// Returns true if there is a substitution renaming loans and symbolic values between the two tools
    fn weak_unification(&self, rhs: &Self, subst: &mut Substitution) -> bool {
        for (k, v) in &self.map {
            let Some(v2) = rhs.get(*k) else {
                eprintln!("missing key in rhs");
                return false;
            };

            let res = v.weak_unification(&v2, subst);

            if !res {
                return false;
            }
        }

        true
    }
}

impl Display for Environ<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (k, v) in &self.map {
            write!(f, "{:?}: {}, ", k, v)?;
        }
        write!(f, "}}")
    }
}

enum GhostAction<'tcx> {
    Unfold(Ty<'tcx>),
    Fold(Ty<'tcx>),
}

struct SymState<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    env: Environ<'tcx>,
    ghost_actions: RefCell<Vec<GhostAction<'tcx>>>,
    fresh_loan: Cell<usize>,
    fresh_sym: Cell<usize>,
    locals: &'a LocalDecls<'tcx>,
    body: &'a Body<'tcx>,
}

#[derive(Default)]
struct SymResults<'tcx> {
    envs: HashMap<BasicBlock, Environ<'tcx>>,
    // Ghost actions to take before executing the given location.
    ghost_actions: HashMap<Location, Vec<GhostAction<'tcx>>>,
}

fn replace_sym<'tcx>(this: SymValue<'tcx>, ix: usize, val: SymValue<'tcx>) -> SymValue<'tcx> {
    match &*this {
        SymValueI::Symbolic(_, id) if *id == ix => val,
        SymValueI::Symbolic(_, _) => this,
        SymValueI::Loan(_) => this,
        SymValueI::Borrow(m, id, v) => SymValue::borrow(*m, *id, replace_sym(v.clone(), ix, val)),
        SymValueI::Constructor { id, args, fields, nm } => {
            let fields = fields.iter().map(|f| replace_sym(f.clone(), ix, val.clone())).collect();
            SymValue::constructor(*nm, *id, args, fields)
        }
        SymValueI::Tuple(fields) => {
            let fields = fields.iter().map(|f| replace_sym(f.clone(), ix, val.clone())).collect();
            SymValue::tuple(fields)
        }
        SymValueI::Uninit => this,
        SymValueI::Wild => this,
        SymValueI::Box(inner) => SymValue::box_(replace_sym(inner.clone(), ix, val)),
    }
}

fn fresh_sym<'tcx>(fresh_sym: &Cell<usize>, ty: Ty<'tcx>) -> SymValue<'tcx> {
    let id = fresh_sym.get();
    fresh_sym.set(id + 1);
    SymValue::symbolic(ty, id)
}

impl<'a, 'tcx> SymState<'a, 'tcx> {
    fn fresh_loan(&self) -> LoanId {
        let loan = self.fresh_loan.get();
        let l = LoanId::Id(loan);
        self.fresh_loan.set(loan + 1);
        l
    }

    fn fresh_sym(&self, ty: Ty<'tcx>) -> SymValue<'tcx> {
        fresh_sym(&self.fresh_sym, ty)
    }

    // TODO: Fix this to be able to create new symbolic values / wild / bottom on the fly
    /// A naive, lossy-join between symbolic values.
    fn join_vals(&self, left: &SymValue<'tcx>, right: &SymValue<'tcx>) -> SymValue<'tcx> {
        use SymValueI::*;

        match (&*left.0, &*right.0) {
            // If both are the same, return either
            (_, _) if Rc::ptr_eq(&left.0, &right.0) => left.clone(),

            (_, Uninit) => right.clone(),
            (Uninit, _) => left.clone(),

            (_, Wild) => right.clone(),
            (Wild, _) => left.clone(),

            // Symbolic values are joined to themselves
            (Symbolic(ty1, id1), Symbolic(ty2, id2)) if ty1 == ty2 && id1 == id2 => left.clone(),
            (Symbolic(ty, _), _) => {
                let Some(left) = self.unfold(*ty, None) else { return self.fresh_sym(*ty) };
                self.join_vals(&left, right)
            }
            (_, Symbolic(_, _)) => self.join_vals(right, left),
            // Loans are joined to themselves
            (Loan(id1), Loan(id2)) if id1 == id2 => left.clone(),
            (Loan(id1), Loan(id2)) => {
                let l = if id1 == id2 { *id1 } else { LoanId::Wild };
                SymValue(Rc::new(SymValueI::Loan(l)))
            }

            // Join borrows if they have the same mutability and loan id
            (Borrow(m1, l1, v1), Borrow(m2, l2, v2)) if m1 == m2 => {
                let l = if l1 == l2 { *l1 } else { self.fresh_loan() };
                SymValue::borrow(*m1, l, self.join_vals(v1, v2))
            }

            // Join constructors if they have the same name, id, and args
            (
                Constructor { nm: n1, id: i1, args: a1, fields: f1 },
                Constructor { nm: n2, id: i2, args: a2, fields: f2 },
            ) if n1 == n2 && i1 == i2 && a1 == a2 => {
                let joined_fields =
                    f1.iter().zip(f2.iter()).map(|(f1, f2)| self.join_vals(f1, f2)).collect();
                SymValue::constructor(*n1, *i1, *a1, joined_fields)
            }

            // Join tuples if they have the same length
            (Tuple(t1), Tuple(t2)) if t1.len() == t2.len() => {
                let joined_fields =
                    t1.iter().zip(t2.iter()).map(|(f1, f2)| self.join_vals(f1, f2)).collect();
                SymValue::tuple(joined_fields)
            }

            // Join boxes by joining their contents
            (Box(b1), Box(b2)) => SymValue::box_(self.join_vals(b1, b2)),

            // If no other case matches, return Bot as a fallback
            _ => {
                eprintln!("{right} v {left}");
                SymValue::wild()
            }
        }
    }

    fn join_env(&self, left: &mut Environ<'tcx>, other: &Environ<'tcx>) {
        merge_hashmaps(&mut left.map, &other.map, |a, b| match (a, b) {
            (None, Some(a)) => a.clone(),
            (Some(a), None) => a.clone(),
            (None, None) => SymValue::wild(),
            (Some(a), Some(b)) => self.join_vals(a, b),
        });
    }

    /// Unfold a symbolic value and fully replace it everywhere in the symbolic environment.
    fn unfold(&self, ty: Ty<'tcx>, variant: Option<VariantIdx>) -> Option<SymValue<'tcx>> {
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
                if adt.variants().len() > 1 && variant.is_none() {
                    return None;
                }
                // assert!(adt.variants().len() == 1 || variant.is_some());

                let variant = &adt.variants()[variant.unwrap_or(0u32.into())];
                let fields: Vec<_> = variant
                    .fields
                    .iter()
                    .map(|field| self.fresh_sym(field.ty(self.tcx, substs)))
                    .collect();
                let nm = variant.ident(self.tcx).name;

                if adt.is_box() {
                    SymValue::box_(self.fresh_sym(substs.type_at(0)))
                } else {
                    SymValue::constructor(nm, variant.def_id, substs, fields)
                }
            }
            _ => self.tcx.dcx().fatal("unsupported type"),
        };

        self.ghost_actions.borrow_mut().push(GhostAction::Unfold(ty));
        Some(new_val)
    }

    /// Unfold a symbolic value and fully replace it everywhere in the symbolic environment.
    fn unfold_and_subst(
        &mut self,
        id: usize,
        ty: Ty<'tcx>,
        variant: Option<VariantIdx>,
    ) -> Option<SymValue<'tcx>> {
        let new_val = self.unfold(ty, variant)?;
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
            TyKind::Bool => return SymValue::bot(),
            TyKind::Char => return SymValue::bot(),
            TyKind::Int(_) => return SymValue::bot(),
            TyKind::Uint(_) => return SymValue::bot(),
            TyKind::Float(_) => return SymValue::bot(),
            TyKind::Str => return SymValue::bot(),
            TyKind::Ref(_, _, _) => {
                self.tcx.dcx().fatal("cannot unfold a bottom value of reference type")
            }

            TyKind::Tuple(fields) => {
                let fields = fields.iter().map(|_ty| SymValue::bot()).collect();
                SymValue::tuple(fields)
            }

            TyKind::Adt(adt, substs) => {
                assert!(adt.variants().len() == 1 || variant.is_some());

                let variant = &adt.variants()[variant.unwrap_or(0u32.into())];
                let fields = variant.fields.iter().map(|_ty| SymValue::bot()).collect();
                let nm = variant.ident(self.tcx).name;
                SymValue::constructor(nm, variant.def_id, substs, fields)
            }
            _ => self.tcx.dcx().fatal("unsupported type"),
        };

        new_val
    }

    fn project_value(
        &mut self,
        v: SymValue<'tcx>,
        proj: ProjectionElem<Local, Ty<'tcx>>,
        span: Span,
    ) -> SymValue<'tcx> {
        let v = if let SymValueI::Symbolic(ty, id) = &*v {
            let var = if let ProjectionElem::Downcast(_, idx) = proj { Some(idx) } else { None };
            self.unfold_and_subst(*id, *ty, var).unwrap_or(v)
        } else {
            v
        };

        match proj {
            ProjectionElem::Deref => {
                if let SymValueI::Borrow(_, _, pointed) = &*v {
                    log::info!("dereferencing borrow value; suspicious");
                    return pointed.clone();
                } else if let SymValueI::Box(pointed) = &*v {
                    return pointed.clone();
                } else {
                    self.tcx.dcx().span_fatal(span, format!("dereferenced non-pointer value: {v}"))
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
        place_ty: PlaceTy<'tcx>,
        projs: &[ProjectionElem<Local, Ty<'tcx>>],
        rhs: SymValue<'tcx>,
        span: Span,
    ) -> SymValue<'tcx> {
        if projs.is_empty() {
            return rhs;
        }

        if let SymValueI::Uninit = &*lhs {
            let var =
                if let ProjectionElem::Downcast(_, idx) = projs[0] { Some(idx) } else { None };

            lhs = self.unfold_bot(place_ty.ty, var);
        }

        let proj = projs[0];
        if let SymValueI::Symbolic(ty, id) = &*lhs {
            let var = if let ProjectionElem::Downcast(_, idx) = proj { Some(idx) } else { None };
            lhs = self.unfold_and_subst(*id, *ty, var).unwrap_or(lhs)
        };

        let place_ty = place_ty.projection_ty(self.tcx, proj);
        match proj {
            ProjectionElem::Deref => {
                if let SymValueI::Borrow(m, l, pointed) = &*lhs {
                    return SymValue::borrow(
                        *m,
                        *l,
                        self.update_value(pointed.clone(), place_ty, &projs[1..], rhs, span),
                    );
                }
                if let SymValueI::Box(pointed) = &*lhs {
                    return SymValue::box_(self.update_value(
                        pointed.clone(),
                        place_ty,
                        &projs[1..],
                        rhs,
                        span,
                    ));
                } else {
                    self.tcx.dcx().span_fatal(span, "updating deref of non-borrow value")
                }
            }
            ProjectionElem::Field(ix, _) => match &*lhs {
                SymValueI::Constructor { nm, id, args, fields } => {
                    let updated = self.update_value(
                        fields[ix.as_usize()].clone(),
                        place_ty,
                        &projs[1..],
                        rhs,
                        span,
                    );

                    let mut fields = fields.clone();

                    fields[ix.as_usize()] = updated;

                    SymValue::constructor(*nm, *id, args, fields)
                }
                SymValueI::Tuple(fields) => {
                    let updated = self.update_value(
                        fields[ix.as_usize()].clone(),
                        place_ty,
                        &projs[1..],
                        rhs,
                        span,
                    );

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
                    self.update_value(lhs, place_ty, &projs[1..], rhs, span)
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

    fn write_place(&mut self, lhs: Place<'tcx>, rhs: SymValue<'tcx>, span: Span) {
        let updated = self.update_value(
            self.env.get(lhs.local).unwrap_or(SymValue::bot()),
            PlaceTy::from_ty(self.locals[lhs.local].ty),
            lhs.projection,
            rhs,
            span,
        );

        let updated = updated.fold();

        if let SymValueI::Uninit = &*updated {
            self.env.map.remove(&lhs.local);
        } else {
            self.env.map.insert(lhs.local, updated);
        }
    }

    fn eval_place(&mut self, pl: Place<'tcx>, span: Span) -> SymValue<'tcx> {
        let mut base_val = self.env.get(pl.local).expect("expected environment to contain value");

        // eprintln!("eval place {pl:?}");
        for proj in pl.projection {
            base_val = self.project_value(base_val, proj, span);
        }

        base_val
    }

    fn eval_operand(&mut self, op: &Operand<'tcx>) -> SymValue<'tcx> {
        match op {
            // TODO mark this as either move or not
            Operand::Copy(pl) => self.eval_place(*pl, op.span(self.locals)),
            Operand::Move(pl) => {
                let old_val = self.eval_place(*pl, op.span(self.locals));
                self.write_place(*pl, SymValue::bot(), op.span(self.locals));
                old_val
            }
            Operand::Constant(c) => self.fresh_sym(c.ty()),
        }
    }

    fn eval_rvalue(&mut self, r: &Rvalue<'tcx>, span: Span) -> SymValue<'tcx> {
        match r {
            Rvalue::Use(op) => self.eval_operand(&op),
            Rvalue::Ref(_, m, pl) => {
                let m = match m {
                    BorrowKind::Shared => Mutability::Not,
                    BorrowKind::Fake(_) => self.tcx.dcx().fatal("unsupported: fake borrow"),
                    BorrowKind::Mut { .. } => Mutability::Mut,
                };
                let loan = self.fresh_loan();
                let borrowed = self.eval_place(*pl, span);
                self.write_place(*pl, SymValue::loan(loan), span);

                SymValue::borrow(m, loan, borrowed)
            }
            Rvalue::Discriminant(pl) => self.fresh_sym(pl.ty(self.locals, self.tcx).ty),
            Rvalue::Aggregate(k, fields) => {
                let fields: Vec<_> = fields.iter().map(|f| self.eval_operand(f)).collect();
                match &**k {
                    mir::AggregateKind::Tuple => SymValue::tuple(fields),
                    mir::AggregateKind::Adt(id, varix, substs, _, _) => {
                        let var = &self.tcx.adt_def(id).variants()[*varix];
                        let nm = var.ident(self.tcx).name;

                        SymValue::constructor(nm, var.def_id, substs, fields)
                    }
                    _ => self.tcx.dcx().span_fatal(span, "unsupported aggregate"),
                }
            }
            Rvalue::Cast(_, _, _) => self.fresh_sym(r.ty(self.locals, self.tcx)),
            Rvalue::BinaryOp(_, _) => self.fresh_sym(r.ty(self.locals, self.tcx)),
            Rvalue::CheckedBinaryOp(_, _) => self.fresh_sym(r.ty(self.locals, self.tcx)),
            Rvalue::NullaryOp(_, _) => self.fresh_sym(r.ty(self.locals, self.tcx)),
            Rvalue::UnaryOp(_, _) => self.fresh_sym(r.ty(self.locals, self.tcx)),
            Rvalue::ShallowInitBox(_, _) => self.tcx.dcx().fatal("shallow init box"),
            Rvalue::CopyForDeref(_) => self.tcx.dcx().fatal("copy for deref"),
            Rvalue::Repeat(_, _) => self.tcx.dcx().fatal(" repeat"),
            Rvalue::ThreadLocalRef(_) => self.tcx.dcx().fatal(" thread local ref"),
            Rvalue::AddressOf(_, _) => self.tcx.dcx().fatal(" address of"),
            Rvalue::Len(_) => self.tcx.dcx().fatal("len"),
        }
    }

    fn eval_statement(&mut self, stmt: &Statement<'tcx>) {
        let span = stmt.source_info.span;
        match &stmt.kind {
            mir::StatementKind::Assign(asgn) => {
                let rhs = self.eval_rvalue(&asgn.1, stmt.source_info.span);
                self.write_place(asgn.0, rhs, stmt.source_info.span)
            }
            mir::StatementKind::FakeRead(_) => {
                log::info!("fake read; ignoring");
            }
            mir::StatementKind::SetDiscriminant { .. } => {
                self.tcx.dcx().fatal("set discriminant; unsupported")
            }
            mir::StatementKind::Deinit(_) => todo!(),
            mir::StatementKind::StorageLive(_) => log::info!("storage live; ignoring"),
            mir::StatementKind::StorageDead(local) => self.write_place(
                Place { local: *local, projection: &List::empty() },
                SymValue::bot(),
                span,
            ),
            mir::StatementKind::Retag(_, _) => log::info!("retag; ignoring"),
            mir::StatementKind::PlaceMention(_) => log::info!("place mention; ignoring"),
            mir::StatementKind::AscribeUserType(_, _) => log::info!("ascribe; ignoring"),
            mir::StatementKind::Coverage(_) => log::info!("coverage; ignoring"),
            mir::StatementKind::Intrinsic(_) => todo!(),
            mir::StatementKind::ConstEvalCounter => log::info!("const eval counter; ignoring"),
            mir::StatementKind::Nop => log::info!("nop; ignoring"),
        }
    }

    fn eval_terminator(&mut self, term: &Terminator<'tcx>) -> Vec<BasicBlock> {
        match &term.kind {
            mir::TerminatorKind::Goto { target } => vec![*target],
            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let _ = self.eval_operand(discr);

                targets.all_targets().to_vec()
            }
            mir::TerminatorKind::Return => vec![],
            mir::TerminatorKind::Unreachable => vec![],
            mir::TerminatorKind::Drop { target, .. } => {
                log::info!("ignoring drop terminator...");
                vec![*target]
            }
            mir::TerminatorKind::Call { func, args, destination, target, .. } => {
                let _ = self.eval_operand(func);

                let _ = args.iter().for_each(|op| {
                    self.eval_operand(&op.node);
                });

                let ret_val = self.fresh_sym(destination.ty(self.locals, self.tcx).ty);
                self.write_place(*destination, ret_val, term.source_info.span);

                vec![target.unwrap()]
            }
            mir::TerminatorKind::FalseEdge { real_target, imaginary_target } => {
                vec![*real_target, *imaginary_target]
            }
            mir::TerminatorKind::Assert { cond, target, .. } => {
                let _ = self.eval_operand(cond);

                vec![*target]
            }
            mir::TerminatorKind::Yield { .. } => self.tcx.dcx().fatal("unhandled terminator Yield"),
            mir::TerminatorKind::UnwindResume => {
                self.tcx.dcx().fatal("unhandled terminator UnwindResume")
            }
            mir::TerminatorKind::UnwindTerminate(_) => {
                self.tcx.dcx().fatal("unhandled terminator UnwindTerminate")
            }
            mir::TerminatorKind::CoroutineDrop => self.tcx.dcx().fatal("unhandled terminator"),
            mir::TerminatorKind::FalseUnwind { real_target, .. } => {
                log::info!("skipping unwind of false unwind");
                vec![*real_target]
            }
            mir::TerminatorKind::InlineAsm { .. } => {
                self.tcx.dcx().fatal("unhandled terminator InlineAsm")
            }
        }
    }

    fn eval_block(&mut self, b: BasicBlock,results: &mut SymResults<'tcx>,) -> Vec<BasicBlock> {
        for s in &self.body[b].statements {
            self.eval_statement(s);
            let _ = std::mem::take(&mut self.ghost_actions);
        }

        let res = self.eval_terminator(self.body[b].terminator());
        // eprintln!("{:?}", self.body[b].terminator().kind);
        // eprintln!("{}", self.env);
        res
    }

    fn eval_body(&mut self, results: &mut SymResults<'tcx>) {
        for a in self.body.args_iter() {
            let fresh = self.fresh_sym(self.locals[a].ty);
            self.env.map.insert(a, fresh);
        }
        results.envs. insert(START_BLOCK, self.env.clone());

        let graph = node_graph(self.body);
        let wto = weak_topological_order(&graph, START_BLOCK);

        for c in wto {
            self.eval_component(results, &c)
        }
    }

    fn eval_component(
        &mut self,
        results: &mut SymResults<'tcx>,
        component: &Component<BasicBlock>,
    ) {
        match component {
            Component::Vertex(bb) => {
                // eprintln!("{bb:?} {}", results.get(bb).unwrap());
                let dests = self.eval_block(*bb, results);
                for d in dests {
                    results.envs
                        .entry(d)
                        .and_modify(|env| self.join_env(env, &self.env))
                        .or_insert_with(|| self.env.clone());
                }
            }
            Component::Component(h, body) => {
                let mut old = results.envs.get(&h).cloned().unwrap();
                let mut num_iter = 0;
                while num_iter < 3 {
                    self.eval_block(*h, results);

                    for b in body {
                        self.eval_component(results, b);
                    }

                    let new = results.envs.get(&h);
                    let new = &**new.as_ref().unwrap();
                    let mut subst = Substitution::default();

                    let unified = old.weak_unification(new, &mut subst);
                    eprintln!("{old}");
                    eprintln!("{new}");
                    eprintln!("{unified}");
                    if !unified {
                        old = new.clone();
                        num_iter += 1;
                    } else {
                        break;
                    }
                }
                self.invariants_between(&old, results.envs.get(&h).unwrap());
            }
        }
    }

    /// Calculate the loop invariant given a state immediately before a loop and a state immediately afterwards.
    fn invariants_between(&self, pre: &Environ<'tcx>, post: &Environ<'tcx>) {
        let mut changed = HashMap::new();
        let mut affected_lifetimes: HashMap<_, HashSet<_>> = HashMap::new();
        for (k, v) in &pre.map {
            if post.get(*k) != Some(v.clone()) {
                changed.insert(k, v);

                let rust_ty = self.body.local_decls[*k].ty;
                let mut col = RegionCollector { regions: Default::default() };
                col.visit_ty(rust_ty);

                for lft in col.regions {
                    affected_lifetimes.entry(lft).or_default().insert(*k);
                }
            }
        }

        eprintln!("needing magic wands {:?}", affected_lifetimes);

        for (lft, vars) in affected_lifetimes {
            let mut out = Vec::new();
            for var in vars {
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
            eprintln!("wand associated to {lft:?}: {wand}");
        }
    }
}

fn diff_terms<'tcx>(
    base: WandTerm,
    l: &SymValue<'tcx>,
    r: &SymValue<'tcx>,
    out: &mut Vec<(WandTerm, WandTerm)>,
) {
    if l == r {
        return;
    }

    match (&**l, &**r) {
        (SymValueI::Symbolic(_, _), SymValueI::Symbolic(_, _)) => {
            out.push((WandTerm::Old(Box::new(base.clone())), base))
        }
        (SymValueI::Loan(_), SymValueI::Loan(_)) => todo!("loan?"),
        (SymValueI::Borrow(_, _, l2), SymValueI::Borrow(_, _, r2)) => {
            diff_terms(WandTerm::Deref(Box::new(base)), l2, r2, out)
        }
        (SymValueI::Constructor { .. }, SymValueI::Constructor { .. }) => todo!(),
        (SymValueI::Tuple(fs), SymValueI::Tuple(gs)) => {
            for (ix, (f, g)) in fs.iter().zip(gs).enumerate() {
                if f == g {
                    continue;
                }

                let base = WandTerm::Field(Box::new(base.clone()), ix.into());
                diff_terms(base, f, g, out)
            }
        }
        (SymValueI::Box(l2), SymValueI::Box(r2)) => {
            diff_terms(WandTerm::Deref(Box::new(base)), l2, r2, out)
        }
        (SymValueI::Wild, SymValueI::Wild) => (),
        (SymValueI::Uninit, SymValueI::Uninit) => (),
        _ => todo!("differing left and rightss"),
    }
}

/// Hrm... should this actually have Place instead? It seems counter productive to do sym value
/// Lets start with a `symvalue ` here even if that's counterproductive in the long term
#[derive(Debug, Clone)]
enum WandTerm {
    Old(Box<WandTerm>),
    Var(Local),
    Deref(Box<WandTerm>),
    Downcast(Box<WandTerm>, VariantIdx, Option<Symbol>),
    Field(Box<WandTerm>, FieldIdx),
    // Tuple(Vec<WandTerm>),
    Conj(Vec<WandTerm>),
    Wand(Box<WandTerm>, Box<WandTerm>),
}

impl<'tcx> std::fmt::Display for WandTerm {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            WandTerm::Conj(ss) => {
                write!(f, "{}", ss[0])?;

                for s in &ss[1..] {
                    write!(f, "/\\ {s}")?;
                }

                Ok(())
            }
            WandTerm::Wand(l, r) => {
                write!(f, "{l} -* {r}")
            }
            WandTerm::Old(w) => write!(f, "old({w})"),
            WandTerm::Var(l) => write!(f, "{l:?}"),
            WandTerm::Deref(w) => write!(f, "* {w}"),
            // WandTerm::Borrow(_, _, _) => todo!(),
            WandTerm::Downcast(w, _ix, sym) => {
                write!(f, "{w}")?;
                if let Some(sym) = sym {
                    write!(f, " as {sym}")?
                };
                Ok(())
            }
            WandTerm::Field(w, ix) => write!(f, "{w} . {}", ix.as_usize()),
            // WandTerm::Box(w) => ,
        }
    }
}

struct RegionCollector {
    regions: HashSet<RegionVid>,
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for RegionCollector {
    fn visit_region(&mut self, _r: Region<'tcx>) -> Self::Result {
        match _r.kind() {
            rustc_type_ir::RegionKind::ReVar(revar) => self.regions.insert(revar),

            _ => todo!("unsupported region type"),
        };
        ()
    }
}

pub(crate) fn node_graph(x: &Body) -> petgraph::graphmap::DiGraphMap<BasicBlock, ()> {
    let mut graph = DiGraphMap::default();
    for (bb, _) in x.basic_blocks.iter_enumerated() {
        if x.basic_blocks[bb].is_cleanup {
            continue;
        }
        graph.add_node(bb);
        for tgt in x.basic_blocks.successors(bb) {
            if x.basic_blocks[tgt].is_cleanup {
                continue;
            }
            graph.add_edge(bb, tgt, ());
        }
    }

    graph
}

pub(crate) fn run_analysis<'tcx>(tcx: TyCtxt<'tcx>, def_id: rustc_hir::def_id::LocalDefId) {
    let a: &BodyWithBorrowckFacts<'tcx> = MIR_BODIES
        .with(|state| {
            let map = state.borrow_mut();
            // SAFETY: For soundness we need to ensure that the bodies have
            // the same lifetime (`'tcx`), which they had before they were
            // stored in the thread local.
            map.get(&def_id).map(|body| unsafe { std::mem::transmute(body) })
        })
        .expect("expected to find body");
    let body = &a.body;
    let mut state = SymState {
        tcx,
        env: Environ { map: Default::default() },
        fresh_loan: Cell::new(0),
        fresh_sym: Cell::new(0),
        locals: &body.local_decls,
        body: &body,
        ghost_actions: RefCell::new(Vec::new())
    };

    let mut results = SymResults::default();

    state.eval_body(&mut results);
}
