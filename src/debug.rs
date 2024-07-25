use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt::Display,
};

use rustc_borrowck::consumers::{
    BodyWithBorrowckFacts, BorrowIndex, RegionInferenceContext, RustcFacts,
};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{traversal::reverse_postorder, BorrowKind, Rvalue, StatementKind},
    ty::{self, Region, RegionVid, TyCtxt, TyKind},
};

use crate::MIR_BODIES;

#[derive(Clone, Debug, PartialEq)]
struct BorrowckState<'a>(
    &'a [BorrowIndex],
    BTreeSet<RegionVid>,
    // Cow<'a, BTreeMap<RegionVid, BTreeSet<RegionVid>>>,
    Cow<'a, BTreeMap<RegionVid, BTreeSet<BorrowIndex>>>,
);

fn state<'a, 'tcx>(
    out: &'a polonius_engine::Output<RustcFacts>,
    regioncx: &RegionInferenceContext<'tcx>,
    reg_reprs: &HashMap<u32, RegionVid>,
    ix: usize,
) -> BorrowckState<'a> {
    let ix = ix.into();

    BorrowckState(
        out.loans_in_scope_at(ix),
        real_origin_live_at(out, regioncx, reg_reprs, ix.into()),
        // out.subsets_at(ix),
        out.origin_contains_loan_at(ix),
    )
}

impl<'a> Display for BorrowckState<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "origins={:?} origins_w_loans={:?}", self.1, self.2)
    }
}

fn real_origin_live_at<'a, 'tcx>(
    out: &'a polonius_engine::Output<RustcFacts>,
    regioncx: &RegionInferenceContext<'tcx>,
    reg_reprs: &HashMap<u32, RegionVid>,
    ix: usize,
) -> BTreeSet<RegionVid> {
    let ix = ix.into();
    let mut live = out.origins_live_at(ix).to_vec();
    let subsets = out.subsets_at(ix);
    let mut flipped_subsets: BTreeMap<_, BTreeSet<_>> = Default::default();
    for (i, subs) in subsets.iter() {
        for s in subs {
            flipped_subsets.entry(s).or_default().insert(i);
        }
    }
    let mut to_expand: Vec<_> = live.iter().cloned().collect();
    to_expand.extend(out.origin_contains_loan_at(ix).keys());
    let mut visited: HashSet<_> = Default::default();
    while let Some(reg) = to_expand.pop() {
        if visited.insert(reg) {
            let supers = flipped_subsets.get(&reg).cloned().unwrap_or_default();
            to_expand.extend(supers.clone());
            live.extend(supers);
        }
    }

    visited
        .into_iter()
        .map(|r| {
            let scc = regioncx.constraint_sccs().scc(r);
            reg_reprs[&scc.as_u32()]
        })
        .collect()
}

pub fn polonius_facts<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) {
    // let a = get_body_with_borrowck_facts(
    //     tcx,
    //     def_id,
    //     rustc_borrowck::consumers::ConsumerOptions::PoloniusOutputFacts,
    // );
    let a: BodyWithBorrowckFacts = MIR_BODIES
        .with(|state| {
            let mut map = state.borrow_mut();
            // SAFETY: For soundness we need to ensure that the bodies have
            // the same lifetime (`'tcx`), which they had before they were
            // stored in the thread local.
            map.remove(&def_id)
                .map(|body| unsafe { std::mem::transmute(body) })
        })
        .expect("expected to find body");

    let reg_ctx = a.region_inference_context;
    let location_table = a.location_table.unwrap();
    let input_facts = a.input_facts.unwrap();

    // Choose a representative for each region cycle
    let mut scc_repr: HashMap<u32, _> = HashMap::new();
    for (reg, scc) in reg_ctx.constraint_sccs().scc_indices().iter_enumerated() {
        scc_repr
            .entry(scc.as_u32())
            .and_modify(|pre: &mut RegionVid| *pre = (*pre).min(reg))
            .or_insert(reg);
    }

    // let b = tcx.mir_borrowck(def_id);
    let output_facts =
        polonius_engine::Output::compute(&*input_facts, polonius_engine::Algorithm::Naive, true);

    for (loc, decl) in a.body.local_decls.iter_enumerated() {
        match decl.ty.kind() {
            TyKind::Ref(reg, ty, mut_) => {
                println!("var {:?} : & {reg:?} {mut_:?} {ty:?}", loc,)
            }
            _ => println!("var {:?} : {:?}", loc, decl.ty),
        }
    }
    eprintln!("");

    let base: HashMap<_, _> = input_facts
        .subset_base
        .iter()
        .map(|(src, tgt, _)| (src, tgt))
        .collect();
    // eprintln!("{:?}", input_facts.subset_base);
    // eprintln!("{:?}", output_facts);
    // eprintln!("{:?}", input_facts.subset_base);
    for (bb, bbd) in reverse_postorder(&a.body) {
        println!("{bb:?}");
        let mut loc = bb.start_location();
        for s in &bbd.statements {
            // Before this instruction: start any relevant lifetimes
            {
                let ix = location_table.mid_index(loc);
                let old = location_table.start_index(loc);

                let old_regions =
                    real_origin_live_at(&output_facts, &reg_ctx, &scc_repr, old.into());

                let new_regions =
                    real_origin_live_at(&output_facts, &reg_ctx, &scc_repr, ix.into());

                let old = state(&output_facts, &reg_ctx, &scc_repr, old.into());
                let ix_state = state(&output_facts, &reg_ctx, &scc_repr, ix.into());
                if old != ix_state {
                    eprintln!("{old}");
                }

                eprintln!("{ix_state}");

                let news: BTreeSet<_> = new_regions.difference(&old_regions).collect();
                if !news.is_empty() {
                    print!("  newlft(");
                    for r in news {
                        print!("{r:?}, ");
                    }
                    println!(")");
                }
            }
            // Instruction
            match &s.kind {
                StatementKind::Assign(b) => match &**b {
                    (l, Rvalue::Ref(reg, kind, r)) => {
                        let mut_ = match kind {
                            BorrowKind::Mut { .. } => "mut",
                            BorrowKind::Shared => "shared",
                            BorrowKind::Fake(_) => "fake(_)",
                            // BorrowKind::Shallow => "shallow",
                            // BorrowKind::Unique => "unique",
                        };

                        let reg = if let ty::ReVar(vid) = reg.kind() {
                            let scc = reg_ctx.constraint_sccs().scc(vid);
                            let vid = scc_repr[&scc.as_u32()];
                            Region::new_var(tcx, vid)
                        } else {
                            *reg
                        };
                        // eprintln!("{:?}", subsets.get(reg));
                        println!("  {l:?} = & {reg:?} {mut_} {r:?}");
                    }
                    _ => println!("  {s:?}"),
                },
                _ => println!("  {s:?}"),
            };

            let old = loc;
            loc = loc.successor_within_block();

            // Kill all dying lifetimes
            {
                let old = location_table.mid_index(old);
                let ix = location_table.start_index(loc);

                let old_regions =
                    real_origin_live_at(&output_facts, &reg_ctx, &scc_repr, old.into());

                let new_regions =
                    real_origin_live_at(&output_facts, &reg_ctx, &scc_repr, ix.into());

                let deads: BTreeSet<_> = old_regions.difference(&new_regions).collect();
                if !deads.is_empty() {
                    print!("  endlft(");
                    for r in deads {
                        print!("{r:?}, ");
                    }
                    println!(")");
                }
            }
        }

        println!("  {:?}", bbd.terminator().kind);
        println!("");
    }
}
