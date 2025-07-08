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
    True,
}

impl std::fmt::Display for ComparisonOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let c = match self {
            ComparisonOp::Gt => '>',
            ComparisonOp::Ge => '≥',
            ComparisonOp::Eq => '=',
            ComparisonOp::Le => '≤',
            ComparisonOp::Lt => '<',
            ComparisonOp::True => ' ',
        };
        write!(f, "{c}")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Branch {
    op: ComparisonOp,
    threshold: Expression,
    value: Expression,
}

impl Branch {
    /// Make an "else" (always-true) branch.
    fn make_else(value: Expression) -> Branch {
        Branch {
            op: ComparisonOp::True,
            threshold: Expression::Modifier(usize::MAX),
            value,
        }
    }
}

impl std::fmt::Display for Branch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let ComparisonOp::True = self.op {
            write!(f, "{{ {} }}", self.value)
        } else {
            write!(f, "{{ {} {} : {} }}", self.op, self.threshold, self.value)
        }
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
    Case {
        target: Box<Expression>,
        branches: Vec<Branch>,
    },
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
            Expression::Case { target, branches } => Expression::Case {
                target: Box::new(target.simplify()),
                branches: branches
                    .into_iter()
                    .map(
                        |Branch {
                             op,
                             threshold,
                             value,
                         }| {
                            Branch {
                                op,
                                threshold: threshold.simplify(),
                                value: value.simplify(),
                            }
                        },
                    )
                    .collect(),
            },
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
            Expression::Case { target, branches } => {
                target.with_paren(f)?;
                for branch in branches {
                    write!(f, " {branch}")?;
                }
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

        rule branch() -> Branch
            = space() "{" space()
                op:compare_op() space() threshold:expression() space()
                ":" space() value:expression() space()
            "}" { Branch{op, threshold, value} }

        rule else_branch() -> Branch
            = space() "{" space() value:expression() space() "}" {
                Branch::make_else(value)
            }

        rule case() -> Expression
            = target:paren() branches:branch()+ el:else_branch()? {
                let mut branches = branches;
                if let Some(el) = el {
                    branches.push(el);
                }
                Expression::Case{ target: Box::new(target), branches }
        }

        pub(crate) rule expression() -> Expression
            = space() e:case() space() { e }
            / space() e:sum() space() { e }
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
        let got: Expression = "(d4){ <= 3: 1}".parse().unwrap();
        let want = Expression::Case {
            target: Box::new(Expression::Die(4)),
            branches: vec![Branch {
                op: ComparisonOp::Le,
                threshold: Expression::Modifier(3),
                value: Expression::Modifier(1),
            }],
        };
        assert_eq!(got, want);
    }

    #[test]
    fn spell_damage() {
        for expr in [
            // fireball, 5th level
            "(1d20+3){>=17:2d10}",
            // eldritch blast, 5th level
            "2 ((1d20+3) { >= 17: 1d10 } )",
            // sacred flame; save
            "(1d20+2){ <= 15: 2d8}",
        ] {
            let _: Expression = expr
                .parse()
                .unwrap_or_else(|err| panic!("failure to parse {expr}: {err}"));
        }
    }

    #[test]
    fn save_for_half() {
        let _: Expression = "(1d20+2){ >= 17: 8d6 /_ 2} { 8d6 }".parse().unwrap();
    }

    fn nontrivial_comparison() -> impl Strategy<Value = ComparisonOp> {
        prop_oneof![
            Just(ComparisonOp::Lt),
            Just(ComparisonOp::Le),
            Just(ComparisonOp::Eq),
            Just(ComparisonOp::Ge),
            Just(ComparisonOp::Gt),
        ]
    }

    // Generate a nontrivial (i.e. "else") branch
    fn branch(expr: impl Clone + Strategy<Value = Expression>) -> impl Strategy<Value = Branch> {
        (nontrivial_comparison(), expr.clone(), expr).prop_map(|(op, threshold, value)| Branch {
            op,
            threshold,
            value,
        })
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
                (
                    strat.clone(),
                    prop::collection::vec(branch(strat.clone()), 1..3),
                    prop::option::of(strat.clone()),
                )
                    .prop_map(|(target, branches, use_else)| {
                        let mut branches = branches;
                        if let Some(v) = use_else {
                            branches.push(Branch::make_else(v))
                        };
                        Expression::Case {
                            target: Box::new(target),
                            branches,
                        }
                    })
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
