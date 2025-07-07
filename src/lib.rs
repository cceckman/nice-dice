//! Utilities for working with dice notation.

use std::str::FromStr;

use discrete::Distribution;
use maud::PreEscaped;
use peg::{error::ParseError, str::LineCol};
use wasm_bindgen::prelude::*;

pub mod discrete;

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

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
enum Ranker {
    All,
    Highest(usize),
    Lowest(usize),
}

impl Ranker {
    /// The minimum count of values required by this ranker.
    fn count(&self) -> usize {
        match self {
            Ranker::All => 0,
            Ranker::Highest(n) => *n,
            Ranker::Lowest(n) => *n,
        }
    }
}

impl std::fmt::Display for Ranker {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (s, n) = match self {
            Ranker::All => return Ok(()),
            Ranker::Highest(n) => ("kh", *n),
            Ranker::Lowest(n) => ("kl", *n),
        };
        if n == 1 {
            write!(f, "{s}")
        } else {
            write!(f, "{s}{n}")
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
enum ComparisonOp {
    Gt,
    Ge,
    Eq,
    Le,
    Lt,
}

impl std::fmt::Display for ComparisonOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let c = match self {
            ComparisonOp::Gt => '>',
            ComparisonOp::Ge => '≥',
            ComparisonOp::Eq => '=',
            ComparisonOp::Le => '≤',
            ComparisonOp::Lt => '<',
        };
        write!(f, "{c}")
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
enum Expression {
    Modifier(usize),
    Die(usize),
    Negated(Box<Expression>),
    Repeated {
        count: Box<Expression>,
        value: Box<Expression>,
        ranker: Ranker,
    },
    Product(Box<Expression>, Box<Expression>),
    Sum(Vec<Expression>),
    Floor(Box<Expression>, Box<Expression>),
    //Ceiling(Box<Expression>, Box<Expression>),
    Comparison(Box<Expression>, ComparisonOp, Box<Expression>),
}

impl Expression {
    fn with_paren(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({self})")
    }
}

impl FromStr for Expression {
    type Err = ParseError<LineCol>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(dice_notation::expression(s)?.simplify())
    }
}

impl Expression {
    fn simplify(self) -> Self {
        match self {
            Expression::Modifier(_) => self,
            Expression::Die(_) => self,
            Expression::Negated(inner) => {
                let simpl = inner.simplify();
                match simpl {
                    Expression::Negated(e) => *e,
                    _ => Expression::Negated(Box::new(simpl)),
                }
            }
            Expression::Repeated {
                count,
                value,
                ranker,
            } => Expression::Repeated {
                count: Box::new(count.simplify()),
                value: Box::new(value.simplify()),
                ranker,
            },
            Expression::Product(a, b) => {
                Expression::Product(Box::new(a.simplify()), Box::new(b.simplify()))
            }
            Expression::Floor(a, b) => {
                Expression::Floor(Box::new(a.simplify()), Box::new(b.simplify()))
            }
            Expression::Sum(expressions) => {
                let mut es = Vec::new();
                for e in expressions.into_iter() {
                    let e = e.simplify();
                    if let Expression::Sum(inner) = e {
                        es.extend(inner)
                    } else {
                        es.push(e)
                    };
                }
                if es.len() == 1 {
                    es.pop().unwrap()
                } else {
                    Expression::Sum(es)
                }
            }
            Expression::Comparison(a, op, b) => {
                Expression::Comparison(Box::new(a.simplify()), op, Box::new(b.simplify()))
            }
        }
    }
}

impl std::fmt::Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Die(n) => write!(f, "d{n}"),
            Expression::Modifier(n) => n.fmt(f),
            Expression::Repeated {
                count,
                value,
                ranker,
            } => {
                if matches!(&**count, Expression::Modifier(_)) {
                    count.fmt(f)?
                } else {
                    count.with_paren(f)?
                };
                if matches!(&**value, Expression::Die(_)) {
                    value.fmt(f)?
                } else {
                    value.with_paren(f)?
                };
                write!(f, "{ranker}")
            }
            Expression::Negated(expression) => {
                if matches!(
                    &**expression,
                    Expression::Modifier(_) | Expression::Die(_) | Expression::Repeated { .. }
                ) {
                    expression.fmt(f)
                } else {
                    expression.with_paren(f)
                }
            }
            Expression::Product(a, b) => {
                if matches!(
                    &**a,
                    Expression::Modifier(_)
                        | Expression::Die(_)
                        | Expression::Repeated { .. }
                        | Expression::Negated(_)
                ) {
                    a.fmt(f)?
                } else {
                    a.with_paren(f)?
                };

                write!(f, " * ")?;

                if matches!(
                    &**b,
                    Expression::Modifier(_)
                        | Expression::Die(_)
                        | Expression::Repeated { .. }
                        | Expression::Negated(_)
                        | Expression::Product(_, _)
                        | Expression::Floor(_, _)
                ) {
                    b.fmt(f)
                } else {
                    b.with_paren(f)
                }
            }
            Expression::Floor(a, b) => {
                if matches!(
                    &**a,
                    Expression::Modifier(_)
                        | Expression::Die(_)
                        | Expression::Repeated { .. }
                        | Expression::Negated(_)
                ) {
                    a.fmt(f)?
                } else {
                    a.with_paren(f)?
                };

                write!(f, " /_ ")?;

                if matches!(
                    &**b,
                    Expression::Modifier(_)
                        | Expression::Die(_)
                        | Expression::Repeated { .. }
                        | Expression::Negated(_)
                        | Expression::Product(_, _)
                        | Expression::Floor(_, _)
                ) {
                    b.fmt(f)
                } else {
                    b.with_paren(f)
                }
            }
            Expression::Sum(es) => {
                fn write_element(
                    e: &Expression,
                    f: &mut std::fmt::Formatter<'_>,
                ) -> Result<(), std::fmt::Error> {
                    let e = match e {
                        Expression::Negated(inner) => inner,
                        _ => e,
                    };
                    match e {
                        Expression::Modifier(_)
                        | Expression::Die(_)
                        | Expression::Repeated { .. }
                        | Expression::Floor(_, _)
                        | Expression::Product(_, _) => e.fmt(f),
                        _ => e.with_paren(f),
                    }
                }
                for (i, e) in es.iter().enumerate() {
                    if i != 0 {
                        let c = if let Expression::Negated(_) = e {
                            '-'
                        } else {
                            '+'
                        };
                        write!(f, " {c} ")?;
                    }
                    write_element(e, f)?;
                }

                Ok(())
            }
            Expression::Comparison(a, op, b) => {
                if matches!(&**a, Expression::Comparison(_, _, _)) {
                    a.with_paren(f)?
                } else {
                    a.fmt(f)?
                };
                write!(f, " {op} ")?;
                if matches!(&**b, Expression::Comparison(_, _, _)) {
                    b.with_paren(f)?
                } else {
                    b.fmt(f)?
                };
                Ok(())
            }
        }
    }
}

peg::parser! {
    grammar dice_notation() for str {
        rule number() -> usize
          = n:$(['0'..='9']+) {? n.parse().or(Err("usize")) }

        rule die() -> Expression
            = "d" n:number() { Expression::Die(n) }

        rule modifier() -> Expression
            = n:number() { Expression::Modifier(n) }

        rule paren() -> Expression
            = "(" space() e:expression() space() ")" { e }
            // / "[" e:expression() "]" { e }
            // / "{" e:expression() "}" { e }

        rule repeatable() -> Expression
            = paren() / die()

        rule repetitions() -> Expression
            = n:number() { Expression::Modifier(n) }
            / paren()

        rule repeat() -> Expression
            = count:repetitions() space() expr:repeatable() rank:ranker()? {
                Expression::Repeated{count: Box::new(count), value: Box::new(expr), ranker: rank.unwrap_or(Ranker::All)} }

        rule ranker() -> Ranker
            = "kl" n:number()? { Ranker::Lowest(n.unwrap_or(1)) }
            / "kh" n:number()? { Ranker::Highest(n.unwrap_or(1)) }

        rule space() = quiet!{[' ' | '\n' | '\r' | '\t']*}

        rule subterm() -> Expression
            =   repeat() / die() / modifier() / paren()
            /   "-" e:(repeat() / die() / modifier() / paren()) { Expression::Negated(Box::new(e)) }

        rule term() -> Expression
            = e1:subterm() space() "*" space() e2:term() { Expression::Product(Box::new(e1), Box::new(e2)) }
            / e1:subterm() space() "/_" space() e2:term() { Expression::Floor(Box::new(e1), Box::new(e2)) }
            // e1:subterm() space() "/^" space() e2:subterm() { Expression::Ceiling(e1, e2) }
            / subterm()

        rule sum_tail() -> Expression
            = space() "-" space() e2:term() { Expression::Negated(Box::new(e2)) }
            / space() "+" space() e2:term() { e2 }

        rule sum() -> Expression
            = e1:term() e2:sum_tail()+ { Expression::Sum(std::iter::once(e1).chain(e2.into_iter()).collect()) }
            / term()

        rule compare_op() -> ComparisonOp
            // Note: order matters! Match the longer >= sequences first.
            = (">=" / "≥") { ComparisonOp::Ge }
            / ">" { ComparisonOp::Gt }
            / "=" { ComparisonOp::Eq }
            / ("<=" / "≤") { ComparisonOp::Le }
            / "<" { ComparisonOp::Lt }

        // TODO: There's a few mechanics that involve fancier conditionals:
        // - save for half damage
        // - critical hit, critical miss
        // Consider... {expr} (cmp expr){value} (cmp expr){value}
        // or some other special grammar for this.
        rule comparison() -> Expression
            = a:sum() space() op:compare_op() space() b:sum() { Expression::Comparison(Box::new(a), op, Box::new(b)) }
            / sum()

        pub(crate) rule expression() -> Expression
            = comparison()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn sole_die() {
        let got: Expression = "d6".parse().unwrap();
        let want = Expression::Die(6);
        assert_eq!(got, want);
    }

    #[test]
    fn several_dice() {
        let got: Expression = "1d20".parse().unwrap();
        let want = Expression::Repeated {
            count: Box::new(Expression::Modifier(1)),
            value: Box::new(Expression::Die(20)),
            ranker: Ranker::All,
        };
        assert_eq!(got, want);
    }

    #[test]
    fn modifier() {
        let got: Expression = "3".parse().unwrap();
        let want = Expression::Modifier(3);
        assert_eq!(got, want);
    }

    #[test]
    fn multiply_chain() {
        let got: Expression = "3 * 4 * 5".parse().unwrap();
        let want = Expression::Product(
            Box::new(Expression::Modifier(3)),
            Box::new(Expression::Product(
                Box::new(Expression::Modifier(4)),
                Box::new(Expression::Modifier(5)),
            )),
        );

        assert_eq!(got, want);
    }

    #[test]
    fn disadvantage() {
        let got: Expression = "2d20kl".parse().unwrap();
        let want = Expression::Repeated {
            count: Box::new(Expression::Modifier(2)),
            value: Box::new(Expression::Die(20)),
            ranker: Ranker::Lowest(1),
        };
        assert_eq!(got, want);
    }

    #[test]
    fn stats_roll() {
        let got: Expression = "4d6kh3".parse().unwrap();
        let want = Expression::Repeated {
            count: Box::new(Expression::Modifier(4)),
            value: Box::new(Expression::Die(6)),
            ranker: Ranker::Highest(3),
        };
        assert_eq!(got, want);
    }

    #[test]
    fn negative() {
        let got: Expression = "-4".parse().unwrap();
        let want = Expression::Negated(Box::new(Expression::Modifier(4)));
        assert_eq!(got, want);
    }

    #[test]
    fn multiply() {
        let got: Expression = "4 * d6".parse().unwrap();
        let want = Expression::Product(
            Box::new(Expression::Modifier(4)),
            Box::new(Expression::Die(6)),
        );
        assert_eq!(got, want);
    }

    #[test]
    fn sum() {
        let got: Expression = "d4 + d6".parse().unwrap();
        let want = Expression::Sum(vec![Expression::Die(4), Expression::Die(6)]);
        assert_eq!(got, want);
    }

    #[test]
    fn compare() {
        let got: Expression = "d4 < d6".parse().unwrap();
        let want = Expression::Comparison(
            Box::new(Expression::Die(4)),
            ComparisonOp::Lt,
            Box::new(Expression::Die(6)),
        );
        assert_eq!(got, want);
    }

    #[test]
    fn spell_damage() {
        for expr in [
            // fireball, 5th level
            "(1d20+3 >= 17) * 2d20",
            // eldritch blast, 5th level
            "2 ( (1d20+3 >= 17) * 2d20)",
            // sacred flame; save
            "(1d20+2 <= 15) * 2d8",
            // fireball, 3rd level, save for half damage
            "((1d20+2 <= 15) + 1) * (8d6) /_ 2",
        ] {
            let _: Expression = expr
                .parse()
                .unwrap_or_else(|_| panic!("failure to parse: {expr}"));
        }
    }

    /// Generate a possibly-recursive Expression.
    fn recursive_expression() -> impl Strategy<Value = Expression> {
        let leaf = proptest::prop_oneof![
            any::<usize>().prop_map(Expression::Die),
            any::<usize>().prop_map(Expression::Modifier),
        ];
        leaf.prop_recursive(3, 2, 3, |strat| {
            prop_oneof![
                (strat.clone(), strat.clone(), any::<Ranker>()).prop_map(
                    |(count, value, ranker)| Expression::Repeated {
                        count: Box::new(count),
                        value: Box::new(value),
                        ranker
                    }
                ),
                (strat.clone(), strat.clone()).prop_map(|(count, value)| {
                    Expression::Product(Box::new(count), Box::new(value))
                }),
                prop::collection::vec(strat.clone(), 2..5).prop_map(Expression::Sum),
                (strat.clone(), strat.clone(), any::<ComparisonOp>())
                    .prop_map(|(a, b, op)| Expression::Comparison(Box::new(a), op, Box::new(b))),
            ]
        })
    }

    proptest! {
        #[test]
        fn expression_roundtrip(exp in recursive_expression()) {
            let s = exp.to_string();
            let got: Expression = s.parse().unwrap();
            assert_eq!(got.simplify(), exp.simplify());
        }
    }

    proptest! {
        #[test]
        fn expression_without_space(exp in recursive_expression()) {
            let s = exp.to_string();
            let s : String = s.chars().filter(|c| *c != ' ').collect();
            let got: Expression = s.parse().unwrap();
            let got_simpl = got.clone().simplify();
            let want_simpl = exp.simplify();
            assert_eq!(got_simpl, want_simpl, "\n{got}\n{s}");
        }
    }
}
