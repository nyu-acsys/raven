use std::io::{Error, ErrorKind};
use std::path::{Path, PathBuf};
use std::collections::VecDeque;
use std::collections::HashSet;
use std::process::Command;

fn all_test_files() -> std::io::Result<Vec<PathBuf>> {
    let mut out = Vec::new();
    let cwd = std::env::current_dir()?;
    let mut map = HashSet::from([cwd.clone()]);
    let mut queue = VecDeque::from([cwd]);
    while let Some(dir) = queue.pop_back() {
        for entry in walkdir::WalkDir::new(&dir).into_iter().filter_map(|e| e.ok()) {
            if entry.path().is_dir() && !map.contains(entry.path()) {
                map.insert(entry.path().to_owned());
                queue.push_back(entry.path().to_owned());
            } else if let Some(filename) = entry.file_name().to_str() {
                if filename.ends_with(".t") {
                    let without_extension = &filename[0..filename.len() - 2];
                    let raven_file = format!("{}.rav", without_extension);
                    let raven_path = entry.path().parent()
                        .ok_or(Error::new(ErrorKind::NotFound, format!("parent directory of file {} not found", entry.path().to_str().unwrap_or("UNFORMATTABLE"))))?
                        .join(raven_file);
                    if Path::is_file(&raven_path) {
                        out.push(raven_path)
                    }
                }
            }
        }
    }
    Ok(out)
}

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
