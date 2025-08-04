//! Dicer CLI.
//!
//! Accepts a dice expression on stdin.
//! Prints an HTML table to stdout, using classes from charts.css.

use std::io::{Read, Write};

use dicer::Closed;

fn main() {
    let mut input = String::new();
    std::io::stdin()
        .lock()
        .read_to_string(&mut input)
        .expect("failed to read input from stdin");
    let expr: Closed = input.parse().expect("invalid expression");
    let distr = expr.distribution().expect("incomputable distribution");
    let figure = dicer::html::figure(&expr, &distr);

    let mut stdout = std::io::stdout().lock();
    write!(stdout, "{}", figure.into_string()).unwrap();
    stdout.flush().unwrap();
}
