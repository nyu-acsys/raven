extern crate tree_sitter;
use std::io::{Read, Write};

use topiary_core::{Language, TopiaryQuery, formatter};


pub fn raven_queries() -> &'static str {
    include_str!("../queries/indent.scm")
}

pub fn format(queries: &str, mut input: impl Read, mut output: impl Write) {
    let grammar = tree_sitter_raven::language().into();
    let query = TopiaryQuery::new(&grammar, queries).unwrap();
    let language = Language { name: "raven".to_owned(), query, grammar, indent: None };
    formatter(&mut input, &mut output, &language, topiary_core::Operation::Format { skip_idempotence: true, tolerate_parsing_errors: true }).unwrap();
}
