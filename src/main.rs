#![feature(rustc_private)]
extern crate rustc_driver;

use std::env;

use polonius_demo::PoloniusDemo;
use rustc_driver::RunCompiler;

fn main() {
    let mut args = env::args().collect::<Vec<_>>();
    args.push("-Cpanic=abort".into());
    args.push("-Coverflow-checks=off".into());
    RunCompiler::new(&args, &mut PoloniusDemo).run().unwrap()
}
