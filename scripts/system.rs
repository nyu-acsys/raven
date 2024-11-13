use std::fs::File;
use std::io::{Error, ErrorKind, Read};
use std::path::{Path, PathBuf};
use std::collections::VecDeque;
use std::collections::HashSet;

pub fn all_test_files() -> std::io::Result<Vec<PathBuf>> {
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

pub fn read_file<P: AsRef<Path>>(path: P, s: &mut String) -> std::io::Result<()> {
    let mut file = File::open(path)?;
    s.clear();
    file.read_to_string(s)?;
    Ok(())
}
