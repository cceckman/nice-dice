#![doc=include_str!("../README.md")]

use std::collections::HashSet;

use maud::PreEscaped;
use peg::{error::ParseError, str::LineCol};
use symbolic::Symbol;

mod analysis;
mod discrete;
mod parse;
mod symbolic;

pub mod html;
pub use analysis::Closed;
pub use discrete::{Distribution, Evaluator};

#[cfg(test)]
mod properties;

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("parse error; in expression {0}; {1}")]
    ParseError(String, ParseError<LineCol>),
    #[error("count cannot be negative; in expression {0}")]
    NegativeCount(String),
    #[error("asked to keep {0} rolls, but the expression {1} may not generate that many")]
    KeepTooFew(usize, String),
    #[error("denominator contains 0 in its range; in expression {0}")]
    DivideByZero(String),
    #[error("invalid character {0} in symbol; symbols may only contain A-Z")]
    InvalidSymbolCharacter(char),
    #[error("symbol(s) used when not bound: {}", list_symbols(.0))]
    UnboundSymbols(HashSet<Symbol>),
    #[error("d0 is not a valid die")]
    ZeroFacedDie(),
}

fn list_symbols(s: &HashSet<Symbol>) -> String {
    let strs: Vec<_> = s.iter().map(|v| v.to_string()).collect();
    strs.join(", ")
}

/// Present the comma-separated expressions as a table, formatted as a column chart by Charts.css.
///
/// Returns a string of HTML indicating. On error, returns HTML indicating the error.
pub fn distribution_table(input: String) -> String {
    match distribution_table_inner(input) {
        Ok(v) => v,
        Err(e) => maud::html!(
            p{ "Error: " (e) }
        ),
    }
    .into()
}

/// Present the comma-separated expressions as a table, formatted as a column chart by Charts.css.
///
/// On success, returns a string of HTML indicating.
pub fn distribution_table_inner(input: String) -> Result<PreEscaped<String>, Error> {
    let items = input.split(",");
    let res: Result<Vec<_>, _> = items
        .map(|v| {
            let expr: Closed = v.parse()?;
            let distr = expr.distribution()?;
            Ok((expr.to_string(), distr))
        })
        .collect();
    let res = res?;

    Ok(html::table_multi_dist(&res))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn readme_examples() {
        // Manual rather than doctest, because it's also a normal .md file
        for expr in [
            "(1d20 + 4 >= 12) * (1d4 + 1)",
            "[ATK: 1d20] (ATK + 4 >= 12) * (1d4 + 1)",
            "[ATK: 1d20] (ATK > 1) * (ATK + 4 >= 12) * (1d4 + 1)",
            "(1d20 > 1) * (1d20 + 4 >= 12) * (1d4 + 1)",
            "[ATK: 1d20] (ATK = 20) * (2d4 + 1) + (ATK < 20) * (ATK > 1) * (ATK + 4 >= 12) * (1d4 + 1)",
            "2([ATK: 1d20] (ATK = 20) * (2d4 + 1) + (ATK < 20) * (ATK > 1) * (ATK + 4 >= 12) * (1d4 + 1))",
            r#"[MOD: +5] [PROFICIENCY: +3] [AC: 12]
2 (
     [ATK: 2d20kl] [DIE: 1d10] [CRIT: 1d10] 
     (ATK = 20) * (DIE + CRIT + MOD) +
     (ATK < 20) * (ATK > 1) (ATK + MOD + PROFICIENCY >= AC) * (DIE + MOD)
)"#,
        ] {
            let _: Closed = expr.parse().unwrap();
        }
    }
}
