use std::process::{Command, exit};

fn main() -> std::io::Result<()> {
    println!("cargo::rerun-if-changed=tools/tree-sitter-raven/grammar.js");
    exit(Command::new("make").arg("-C").arg("tools/tree-sitter-raven/").spawn().expect("Failed to run ravenfmt").wait()?.code().unwrap());
}
