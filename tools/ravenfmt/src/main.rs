extern crate string_builder;
extern crate walkdir;
mod format;
use format::format;
use format::raven_queries;

use std::io::BufRead;
use std::io::BufWriter;
use std::path::{PathBuf, Path};
use clap::Parser;
use std::fs::File;
use std::io::BufReader;
use string_builder::Builder;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
/// The command line arguments.
struct Args {
    /// When this argument is passed, the default configuration will
    /// be  printed to the console output.
    #[clap(long, short, action)]
    default_config: bool,
    /// When this argument is passed, the outputs will be printed
    /// to the console output, instead of to file.
    #[clap(long, short, action)]
    print_outputs: bool,
    /// When this argument is passed, the configuration file passed
    /// will be used. Otherwise, either the nearest "indents.scm"
    /// file will be used, or, if the "indents.scm" file is not found,
    /// the default configuration will be used.
    #[clap(long, short)]
    config_file: Option<PathBuf>,
    /// The file(s) to format. When unavailable, console input is used.
    files: Vec<PathBuf>,
}

fn read_file(file: &PathBuf) -> std::io::Result<String> {
    let f = File::open(file)?;
    let mut r = BufReader::new(f);
    let mut buf = Builder::default();
    let mut temp = String::new();
    let mut input_left = true;
    while input_left {
        let len = r.read_line(&mut temp)?;
        buf.append(std::mem::take(&mut temp));
        input_left = len > 0;
    }
    buf.string().map_err(|_| std::io::Error::new(std::io::ErrorKind::Other, "bad utf8"))
}

fn find_config() -> Option<std::io::Result<PathBuf>> {
    let cwd = std::env::current_dir().ok()?;
    for ancestor in Path::ancestors(&cwd) {
        for entry in walkdir::WalkDir::new(ancestor).into_iter().filter_map(|e| e.ok()).filter(|e| Path::new(e.path()).is_file()) {
            if entry.file_name().to_str()?.eq("indent.scm") {
                return Some(Ok(entry.path().to_owned()))
            }
        }
    }
    None
}

fn main() {
    let cli = Args::parse();
    if cli.default_config {
        eprintln!("{}", format::raven_queries());
        return;
    }

    let config = cli.config_file.map(Ok)
        .or(find_config()).
        map_or_else(|| raven_queries().to_owned(), |f| read_file(&f.unwrap()).unwrap());

    if cli.files.len() == 0 {
        format(&config, std::io::stdin(), std::io::stdout());
    } else {
        for file in cli.files {
            let s = read_file(&file).unwrap();
            if cli.print_outputs {
                format(&config, s.as_bytes(), std::io::stdout());
            } else {
                format(&config, s.as_bytes(), BufWriter::new(File::create(file).unwrap()));
            }
        }
    }
}
