#![feature(rustc_private, register_tool)]
#![feature(box_patterns, control_flow_enum)]
#![feature(let_chains, never_type, try_blocks)]

use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

use rustc_borrowck::consumers::{
    get_body_with_borrowck_facts, BodyWithBorrowckFacts, ConsumerOptions,
};
use rustc_hir::def_id::LocalDefId;
use rustc_interface::Config;
use rustc_middle::{
    mir::{traversal::reverse_postorder, BorrowKind, Rvalue, StatementKind},
    ty::{self, Region, Ty, TyCtxt, TyKind},
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
    eprintln!("{:?}", output_facts);
    // eprintln!("{:?}", input_facts.subset_base);
    for (bb, bbd) in reverse_postorder(&a.body) {
        println!("{bb:?}");
        let mut loc = bb.start_location();
        for s in &bbd.statements {
            // Before this instruction: start any relevant lifetimes
            {
                let ix = location_table.mid_index(loc);
                let old = location_table.start_index(loc);

                let mut old_regions: HashSet<_> =
                    output_facts.origins_live_at(old).iter().collect();
                let old_derived = output_facts.origin_contains_loan_at(old);
                old_regions.extend(old_derived.keys());
                let mut new_regions: HashSet<_> = output_facts.origins_live_at(ix).iter().collect();
                let ix_derived = output_facts.origin_contains_loan_at(ix);
                new_regions.extend(ix_derived.keys());

                eprintln!(
                    "loans={:?} origins={:?} subsets={:?} origin_contains={:?}",
                    output_facts.loans_in_scope_at(old),
                    output_facts.origins_live_at(old),
                    output_facts.subsets_at(old),
                    output_facts.origin_contains_loan_at(old)
                );

                eprintln!(
                    "loans={:?} origins={:?} subsets={:?} origin_contains={:?}",
                    output_facts.loans_in_scope_at(ix),
                    output_facts.origins_live_at(ix),
                    output_facts.subsets_at(ix),
                    output_facts.origin_contains_loan_at(ix)
                );

                for r in new_regions.difference(&old_regions) {
                    println!("  newlft({r:?})");
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

                let mut old_regions: HashSet<_> =
                    output_facts.origins_live_at(old).iter().collect();
                let old_derived = output_facts.origin_contains_loan_at(old);
                old_regions.extend(old_derived.keys());

                let mut new_regions: HashSet<_> = output_facts.origins_live_at(ix).iter().collect();
                let ix_derived = output_facts.origin_contains_loan_at(ix);
                new_regions.extend(ix_derived.keys());

                for r in old_regions.difference(&new_regions) {
                    println!("  endlft({r:?})");
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
