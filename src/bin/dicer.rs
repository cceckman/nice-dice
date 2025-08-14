//! nice-dice CLI.
//!
//! Accepts a dice expression on stdin.
//! Prints an HTML table to stdout, using classes from charts.css.

use std::io::{Read, Write};

fn main() {
    let mut input = String::new();
    std::io::stdin()
        .lock()
        .read_to_string(&mut input)
        .expect("failed to read input from stdin");
    let figure = nice_dice::distribution_table_inner(input).unwrap();

    let mut stdout = std::io::stdout().lock();
    write!(stdout, "{}", figure.into_string()).unwrap();
    stdout.flush().unwrap();
}
