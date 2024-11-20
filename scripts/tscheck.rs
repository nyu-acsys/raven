mod system;
use system::{all_test_files, read_file};
use std::io::{Error, ErrorKind};
use tree_sitter_raven::language;
use std::collections::VecDeque;

fn parse_status<S: AsRef<[u8]>>(parser: &mut tree_sitter::Parser, buf: S) -> std::io::Result<String> {
    match parser.parse(buf, None) {
        None => Err(Error::new(ErrorKind::Other, "Parse error: no parse tree could be created")),
        Some(tree) => {
            let mut queue = VecDeque::from([tree.root_node()]);
            while let Some(node) = queue.pop_back() {
                if node.is_error() {
                    let msg = format!("Error at {}-{}", node.start_position(), node.end_position());
                    return Err(Error::new(ErrorKind::Other, msg));
                }
                let mut cursor = node.walk();
                for child in node.children(&mut cursor) {
                    queue.push_front(child);
                }
            }
            Ok("success".to_string())
        }
    }
}

/// Find all .rav files, and run "rustfmt" on them.
fn main() -> std::io::Result<()> {
    let mut buf = String::new();
    for file in all_test_files()? {
        let file_name = file.clone().into_os_string().into_string().map_err(|e| Error::new(ErrorKind::Other, format!("could not format {:?} as string", e)))?;
        println!("checking {}", file_name);
        read_file(&file, &mut buf)?;
        let mut parser = tree_sitter::Parser::new();
        parser.set_language(&language()).map_err(|e| Error::new(ErrorKind::Other, format!("{:?}", e)))?;
        let parse_status = parse_status(&mut parser, &buf.as_bytes())?;
        println!("parse status: {}", parse_status);
    }
    Ok(())
}
