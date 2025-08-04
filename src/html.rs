//! HTML formatting for dice expressions and distributions, mostly distributions.

use crate::Distribution;

/// A table showing the various distributions as bar charts.
pub fn table_multi_dist(inputs: &[(impl AsRef<str>, Distribution)]) -> maud::PreEscaped<String> {
    // We need to know the minimum value, maximum value, and maximum frequency.
    let min = inputs
        .iter()
        .fold(isize::MAX, |acc, (_, dist)| std::cmp::min(acc, dist.min()));
    let max = inputs
        .iter()
        .fold(isize::MIN, |acc, (_, dist)| std::cmp::max(acc, dist.max()));
    let rows = (min..=max)
        .map(|value| -> (isize, Vec<f64>) {
            (
                value,
                inputs
                    .iter()
                    .map(|(_, distr)| distr.probability_f64(value))
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
        table class="charts-css bar [ show-data-on-hover data-start ] multiple show-heading show-labels" style="--labels-size: 16pt"{
            thead {
                @for (name, _) in inputs { th scope="col" { (name.as_ref()) } }
            }
            @for (value, row) in rows.into_iter() {
                tr {
                    th scope="row" { (value) }
                    @for freq in row {
                        @let size = freq / max;
                        td style=(format!("--size: {}", size)) { span class="data" { (format!("{:.1}%", freq * 100.0)) }}
                    }
                }
            }
        }
    }
}
