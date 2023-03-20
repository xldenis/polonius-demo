#![feature(rustc_private)]
extern crate rustc_driver;

use std::env;

use polonius_demo::PoloniusDemo;
use rustc_driver::RunCompiler;

fn main() {
    let args = env::args().collect::<Vec<_>>();

    RunCompiler::new(&args, &mut PoloniusDemo).run().unwrap()
}
