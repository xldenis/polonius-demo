#![feature(rustc_private, register_tool)]
#![feature(box_patterns, control_flow_enum)]
#![feature(let_chains, never_type, try_blocks)]

use std::{cell::RefCell, collections::HashMap};

use rustc_borrowck::consumers::{BodyWithBorrowckFacts, ConsumerOptions};
use rustc_hir::def_id::LocalDefId;
use rustc_interface::Config;
use rustc_middle::ty::TyCtxt;

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

mod debug;
mod aenealite;
mod wto;

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
        debug::polonius_facts(tcx, def_id);
        aenealite::run_analysis(tcx, def_id);
    }
}
