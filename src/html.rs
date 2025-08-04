//! HTML formatting for dice expressions and distributions, mostly distributions.

use crate::{Closed, Distribution};

/// A figure, captioned with the expression, containing the bar chart of the expression.
///
// TODO: Multi-value, with legend
pub fn figure(expr: &Closed, dist: &Distribution) -> maud::PreEscaped<String> {
    let e = expr.to_string();
    maud::html! {
        figure class="dicer" {
            (table_multi_dist(&[&e], &[dist]))

            caption {
                (expr.to_string())
            }
        }
    }
}

/// A table showing the various distributions as bar charts.
pub fn table_multi_dist(inputs: &[&str], distrs: &[&Distribution]) -> maud::PreEscaped<String> {
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
                    .map(|distr| distr.probability_f64(value) * 100.0)
                    .collect(),
            )
        })
        .collect::<Vec<_>>();
    let max = rows
        .iter()
        .flat_map(|(_, v)| v.iter())
        .fold(0.0, |acc, v| if acc > *v { acc } else { *v });

    // TODO: Add charts.css colors
    maud::html! {
        table class="charts-css column [ show-data-on-hover data-start ] show-heading show-labels" style="--labels-size: 10pt"{
            thead {
                @for name in inputs { th scope="col" { (name) } }
            }
            @for (value, row) in rows.into_iter() {
                tr {
                    th scope="row" { (value) }
                    @for freq in row {
                        @let size = freq / max;
                        td style=(format!("--size: {}", size)) { span class="data" { (format!("{freq:.1}%")) }}
                    }
                }
            }
        }
    }
}
