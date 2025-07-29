//! Utilities for working with dice notation.
//!
//! For example, here's the roll for:
//! - A level 5 warlock with +5 Charisma modifier
//! - with the Agonizing Blast feature
//! - casting Eldritch Blast (two beams)
//! - against a creature with armor class 16
//! - including critical effects
//!
//! ```
//! [AC: 16] [CHA: +5] 2([ATK: 1d20] (ATK = 20) * (2d10 + CHA) + (ATK < 20) * (ATK > 1) * (ATK + CHA >= AC) * (1d10 + CHA))";
//! ```

// use discrete::Distribution;
use maud::PreEscaped;
use peg::{error::ParseError, str::LineCol};
use symbolic::Symbol;
use wasm_bindgen::prelude::*;

// pub mod discrete;
mod analysis;
mod parse;
mod symbolic;

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
    #[error("symbol {0} is defined more than once")]
    SymbolRedefined(Symbol),
    #[error("symbol {0} is not defined when used")]
    SymbolUndefined(Symbol),
    #[error("d0 is not a valid die")]
    ZeroFacedDie(),
}

///// Get the distribution of the expression as an HTML table.
//#[wasm_bindgen]
//pub fn distribution_table(inputs: Vec<String>) -> String {
//    match distribution_table_inner(inputs) {
//        Ok(v) => v,
//        Err(e) => maud::html!(
//            p{ "Error: " (e) }
//        ),
//    }
//    .into()
//}
//
//fn distribution_table_inner(inputs: Vec<String>) -> Result<PreEscaped<String>, Error> {
//    fn get_distr(s: &String) -> Result<Distribution, Error> {
//        let e: parse::Expression = s.parse().map_err(|e| Error::ParseError(s.to_owned(), e))?;
//        e.distribution()
//    }
//
//    use web_sys::console;
//
//    console::log_1(&format!("got {} inputs", inputs.len()).into());
//    let distrs: Result<Vec<Distribution>, _> = inputs.iter().map(get_distr).collect();
//    let distrs = distrs?;
//    console::log_1(&format!("got {} outputs", distrs.len()).into());
//
//    // We need to know the minimum value, maximum value, and maximum frequency.
//    let min = distrs
//        .iter()
//        .fold(isize::MAX, |acc, dist| std::cmp::min(acc, dist.min()));
//    let max = distrs
//        .iter()
//        .fold(isize::MIN, |acc, dist| std::cmp::max(acc, dist.max()));
//    let rows = (min..=max)
//        .map(|value| -> (isize, Vec<f64>) {
//            (
//                value,
//                distrs
//                    .iter()
//                    .map(|distr| distr.probability_f64(value))
//                    .collect(),
//            )
//        })
//        .collect::<Vec<_>>();
//    let max = rows
//        .iter()
//        .flat_map(|(_, v)| v.iter())
//        .fold(0.0, |acc, v| if acc > *v { acc } else { *v });
//
//    // TODO: Legend
//    Ok(maud::html! {
//        table class="charts-css column [ show-data-on-hover data-start ] show-heading show-labels" style="--labels-size: 10pt"{
//            thead {
//                @for name in inputs { th scope="col" { (name) } }
//            }
//            @for (value, row) in rows.into_iter() {
//                tr {
//                    th scope="row" { (value) }
//                    @for freq in row {
//                        @let size = freq / max;
//                        td style=(format!("--size: {}", size)) { span class="data" { (format!("{freq:.2}")) }}
//                    }
//                }
//            }
//        }
//    })
//}
