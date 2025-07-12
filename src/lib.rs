//! Utilities for working with dice notation.

use discrete::Distribution;
use maud::PreEscaped;
use peg::{error::ParseError, str::LineCol};
use wasm_bindgen::prelude::*;

pub mod discrete;
mod parse;
use parse::{Branch, ComparisonOp, Expression, Ranker};

#[derive(thiserror::Error, Debug)]
pub enum Error {
    #[error("parse error; in expression {0}; {1}")]
    ParseError(String, ParseError<LineCol>),
    #[error("count cannot be negative; in expression {0}")]
    NegativeCount(String),
    #[error("kept values are fewer than the count; in expression {0}")]
    KeepTooFew(String),
    #[error("denominator contains 0; in expression {0}")]
    DivideByZero(String),
    #[error("invalid character {0} in symbol; symbols may only contain A-Z")]
    InvalidSymbolCharacter(char),
}

/// Get the distribution of the expression as an HTML table.
#[wasm_bindgen]
pub fn distribution_table(inputs: Vec<String>) -> String {
    match distribution_table_inner(inputs) {
        Ok(v) => v,
        Err(e) => maud::html!(
            p{ "Error: " (e) }
        ),
    }
    .into()
}

fn distribution_table_inner(inputs: Vec<String>) -> Result<PreEscaped<String>, Error> {
    fn get_distr(s: &String) -> Result<Distribution, Error> {
        let e: Expression = s.parse().map_err(|e| Error::ParseError(s.to_owned(), e))?;
        e.distribution()
    }

    use web_sys::console;

    console::log_1(&format!("got {} inputs", inputs.len()).into());
    let distrs: Result<Vec<Distribution>, _> = inputs.iter().map(get_distr).collect();
    let distrs = distrs?;
    console::log_1(&format!("got {} outputs", distrs.len()).into());

    // We need to know the minimum value, maximum value, and maximum frequency.
    let min = distrs
        .iter()
        .fold(isize::MAX, |acc, dist| std::cmp::min(acc, dist.min()));
    let max = distrs
        .iter()
        .fold(isize::MIN, |acc, dist| std::cmp::max(acc, dist.max()));
    let rows = (min..=max)
        .map(|value| -> (isize, Vec<f64>) {
            (
                value,
                distrs
                    .iter()
                    .map(|distr| distr.probability_f64(value))
                    .collect(),
            )
        })
        .collect::<Vec<_>>();
    let max = rows
        .iter()
        .flat_map(|(_, v)| v.iter())
        .fold(0.0, |acc, v| if acc > *v { acc } else { *v });

    // TODO: Legend
    Ok(maud::html! {
        table class="charts-css column [ show-data-on-hover data-start ] show-heading show-labels" style="--labels-size: 10pt"{
            thead {
                @for name in inputs { th scope="col" { (name) } }
            }
            @for (value, row) in rows.into_iter() {
                tr {
                    th scope="row" { (value) }
                    @for freq in row {
                        @let size = freq / max;
                        td style=(format!("--size: {}", size)) { span class="data" { (format!("{freq:.2}")) }}
                    }
                }
            }
        }
    })
}
