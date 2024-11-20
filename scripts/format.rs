#![allow(unused)]
mod system;
use system::all_test_files;
use std::process::Command;
use std::io::{Error, ErrorKind};

/// Find all .rav files, and run "rustfmt" on them.
fn main() -> std::io::Result<()> {
    for file in all_test_files()? {
        let file_name = file.file_name().unwrap().to_str().ok_or(Error::new(ErrorKind::Other, "Could reformat file name to utf8"))?;
        println!("formatting {}", file_name);
        let file = file.into_os_string().into_string().map_err(|e| Error::new(ErrorKind::Other, format!("could not format {:?} as string", e)))?;
        println!("running: {}", ["cargo", "run", "-p", "ravenfmt", "--", "-p", &file].join(" "));
        Command::new("cargo").arg("run").arg("-q").arg("-p").arg("ravenfmt").arg("--").arg("-p").arg(file).spawn().expect("Failed to run ravenfmt").wait().expect("failed waiting on rust format process.");

    }
    Ok(())
}
