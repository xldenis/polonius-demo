#![feature(rustc_private, register_tool)]
#![feature(box_patterns, control_flow_enum)]
#![feature(let_chains, never_type, try_blocks)]

use std::{
    borrow::Cow,
    cell::RefCell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
};

use rustc_borrowck::consumers::{
    get_body_with_borrowck_facts, BodyWithBorrowckFacts, BorrowIndex, ConsumerOptions, RustcFacts,
};
use rustc_hir::def_id::LocalDefId;
use rustc_interface::Config;
use rustc_middle::{
    mir::{traversal::reverse_postorder, BorrowKind, Rvalue, StatementKind},
    ty::{self, Region, RegionVid, Ty, TyCtxt, TyKind},
};

// #[macro_use]
extern crate log;
extern crate polonius_engine;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_macros;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_mir_build;
extern crate rustc_mir_dataflow;
extern crate rustc_mir_transform;
extern crate rustc_resolve;
extern crate rustc_serialize;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_type_ir;

#[derive(Clone, Debug, PartialEq)]
struct BorrowckState<'a>(
    &'a [BorrowIndex],
    &'a [RegionVid],
    Cow<'a, BTreeMap<RegionVid, BTreeSet<RegionVid>>>,
    Cow<'a, BTreeMap<RegionVid, BTreeSet<BorrowIndex>>>,
);

fn state<'a>(out: &'a polonius_engine::Output<RustcFacts>, ix: usize) -> BorrowckState<'a> {
    let ix = ix.into();

    BorrowckState(
        out.loans_in_scope_at(ix),
        out.origins_live_at(ix),
        out.subsets_at(ix),
        out.origin_contains_loan_at(ix),
    )
}

fn real_origin_live_at<'a>(
    out: &'a polonius_engine::Output<RustcFacts>,
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

    visited.into_iter().collect()
}

fn polonius_facts<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) {
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

    let location_table = a.location_table.unwrap();
    let input_facts = a.input_facts.unwrap();
    // let entry_block = mir::START_BLOCK;
    // let entry_point = location_table.start_index(mir::Location {
    //     block: entry_block,
    //     statement_index: 0,
    // });
    // for (origin, loan) in &input_facts.placeholder {
    //     input_facts
    //         .loan_issued_at
    //         .push((*origin, *loan, entry_point));
    // }
    // for (origin1, origin2) in &input_facts.known_placeholder_subset {
    //     input_facts
    //         .subset_base
    //         .push((*origin1, *origin2, entry_point));
    // }

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

                let old_regions = real_origin_live_at(&output_facts, old.into());

                // let mut old_regions: HashSet<_> =
                //     output_facts.origins_live_at(old).iter().collect();
                // let old_derived = output_facts.origin_contains_loan_at(old);
                // old_regions.extend(old_derived.keys());

                let new_regions = real_origin_live_at(&output_facts, ix.into());

                // let mut new_regions: HashSet<_> = output_facts.origins_live_at(ix).iter().collect();
                // let ix_derived = output_facts.origin_contains_loan_at(ix);
                // new_regions.extend(ix_derived.keys());

                let old = state(&output_facts, old.into());
                let ix_state = state(&output_facts, ix.into());
                if old != ix_state {
                    // eprintln!(
                    //     "loans={:?} origins={:?} subsets={:?} origin_contains={:?}",
                    //     old.0, old.1, old.2, old.3
                    // );
                }

                // eprintln!(
                //     "loans={:?} origins={:?} subsets={:?} origin_contains={:?} real_origins={:?}",
                //     ix_state.0,
                //     ix_state.1,
                //     ix_state.2,
                //     ix_state.3,
                //     real_origin_live_at(&output_facts, ix.into()),
                // );

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

                        let subsets = output_facts.subsets_at(location_table.mid_index(loc));

                        let reg = if let ty::ReVar(vid) = reg.kind()
                            && let Some(sub) = base.get(&vid)
                        {
                            Region::new_var(tcx, **sub)
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

                let old_regions = real_origin_live_at(&output_facts, old.into());

                let new_regions = real_origin_live_at(&output_facts, ix.into());

                // let mut old_regions: HashSet<_> =
                //     output_facts.origins_live_at(old).iter().collect();
                // let old_derived = output_facts.origin_contains_loan_at(old);
                // old_regions.extend(old_derived.keys());

                // let mut new_regions: HashSet<_> = output_facts.origins_live_at(ix).iter().collect();
                // let ix_derived = output_facts.origin_contains_loan_at(ix);
                // new_regions.extend(ix_derived.keys());


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

    // println!("{:?}", output_facts.origin_live_on_entry);
}

thread_local! {
    pub static MIR_BODIES:
        RefCell<HashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(HashMap::new());
}

use rustc_driver::Callbacks;
use rustc_session::config::OutputFilenames;

pub struct PoloniusDemo;

impl Callbacks for PoloniusDemo {
    fn config(&mut self, config: &mut Config) {
        config.override_queries = Some(|_sess, providers| {
            providers.mir_borrowck = |tcx, def_id| {
                let opts = ConsumerOptions::PoloniusOutputFacts;

                let body_with_facts =
                    rustc_borrowck::consumers::get_body_with_borrowck_facts(tcx, def_id, opts);

                // SAFETY: The reader casts the 'static lifetime to 'tcx before using it.
                let body_with_facts: BodyWithBorrowckFacts<'static> =
                    unsafe { std::mem::transmute(body_with_facts) };

                MIR_BODIES.with(|state| {
                    let mut map = state.borrow_mut();
                    assert!(map.insert(def_id, body_with_facts).is_none());
                });

                (rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_borrowck)(tcx, def_id)
            }
        });
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &rustc_interface::interface::Compiler,
        queries: &'tcx rustc_interface::Queries<'tcx>,
    ) -> rustc_driver::Compilation {
        queries.global_ctxt().unwrap().enter(|tcx| run(tcx));
        rustc_driver::Compilation::Continue
    }
}

fn run<'tcx>(tcx: TyCtxt<'tcx>) {
    for def_id in tcx.hir().body_owners() {
        polonius_facts(tcx, def_id);
    }
}
