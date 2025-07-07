//! Utilities for working with dice notation.

use num::{ToPrimitive, rational::Ratio};
use wasm_bindgen::prelude::*;

pub mod discrete;
/*
/// Get the distribution of the expression as an HTML table.
#[wasm_bindgen]
pub fn distribution_table(inputs: Vec<String>) -> String {
    let e: Result<Vec<_>, _> = inputs.iter().map(|e| expression(e)).collect();

    // We need to know the minimum value, maximum value, and maximum frequency.
    let min = distrs
        .iter()
        .fold(isize::MAX, |acc, dist| std::cmp::min(acc, dist.min()));
    let rows = (min..)
        .map(|value| -> (isize, Vec<f64>) {
            (
                value,
                distrs
                    .iter()
                    .map(|distr| {
                        let prob = distr.probability(value);
                        Ratio::to_f64(&prob).unwrap()
                    })
                    .collect(),
            )
        })
        .take_while(|(_, row)| row.iter().any(|&v: &f64| v != 0.0))
        .collect::<Vec<_>>();
    let max = rows
        .iter()
        .flat_map(|(_, v)| v.iter())
        .fold(0.0, |acc, v| if acc > *v { acc } else { *v });

    // TODO: Legend
    maud::html! {
        table class="charts-css column [ show-data-on-hover data-start ] show-heading show-labels" style="--labels-size: 10pt"{
            thead {
                @for name in strings { th scope="col" { (name) } }
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
    }.into()
}*/

#[derive(PartialEq, Eq, Debug, Clone, Copy)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
enum Ranker {
    All,
    Highest(usize),
    Lowest(usize),
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
    //Floor(Box<Expression>, Box<Expression>),
    //Ceiling(Box<Expression>, Box<Expression>),
    Comparison(Box<Expression>, ComparisonOp, Box<Expression>),
}

impl Expression {
    fn with_paren(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({self})")
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
            = "(" e:expression() ")" { e }
            / "[" e:expression() "]" { e }
            / "{" e:expression() "}" { e }

        rule repeatable() -> Expression
            = die() / paren()

        rule repetitions() -> Expression
            = n:number() { Expression::Modifier(n) }
            / paren()

        rule repeat() -> Expression
            = count:repetitions() expr:repeatable() rank:ranker()? {
                Expression::Repeated{count: Box::new(count), value: Box::new(expr), ranker: rank.unwrap_or(Ranker::All)} }

        rule ranker() -> Ranker
            = "kl" n:number()? { Ranker::Lowest(n.unwrap_or(1)) }
            / "kh" n:number()? { Ranker::Highest(n.unwrap_or(1)) }

        rule space() = quiet!{[' ' | '\n' | '\r' | '\t']*}

        rule subterm() -> Expression
            =   die() / repeat() / modifier() / paren()
            /   "-" e:(die() / repeat() / modifier() / paren()) { Expression::Negated(Box::new(e)) }

        rule term() -> Expression
            = e1:subterm() space() "*" space() e2:subterm() { Expression::Product(Box::new(e1), Box::new(e2)) }
            // e1:subterm() space() "/" space() e2:subterm() { Expression::Floor(e1, e2) }
            // e1:subterm() space() "/^" space() e2:subterm() { Expression::Ceiling(e1, e2) }
            / subterm()

        rule sum_tail() -> Expression
            = space() "-" space() e2:term() { Expression::Negated(Box::new(e2)) }
            / space() "+" space() e2:term() { e2 }

        rule sum() -> Expression
            = e1:term() e2:sum_tail()+ { Expression::Sum(std::iter::once(e1).chain(e2.into_iter()).collect()) }
            / term()

        rule compare_op() -> ComparisonOp
            = ">" { ComparisonOp::Gt }
            / (">=" / "≥") { ComparisonOp::Ge }
            / "=" { ComparisonOp::Eq }
            / ("<=" / "≤") { ComparisonOp::Le }
            / "<" { ComparisonOp::Lt }

        rule comparison() -> Expression
            = a:sum() space() op:compare_op() space() b:sum() { Expression::Comparison(Box::new(a), op, Box::new(b)) }
            / sum()

        pub rule expression() -> Expression
            = comparison()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn sole_die() {
        let got = dice_notation::expression("d6").unwrap();
        let want = Expression::Die(6);
        assert_eq!(got, want);
    }

    #[test]
    fn several_dice() {
        let got = dice_notation::expression("1d20").unwrap();
        let want = Expression::Repeated {
            count: Box::new(Expression::Modifier(1)),
            value: Box::new(Expression::Die(20)),
            ranker: Ranker::All,
        };
        assert_eq!(got, want);
    }

    #[test]
    fn modifier() {
        let got = dice_notation::expression("3").unwrap();
        let want = Expression::Modifier(3);
        assert_eq!(got, want);
    }

    #[test]
    fn disadvantage() {
        let got = dice_notation::expression("2d20kl").unwrap();
        let want = Expression::Repeated {
            count: Box::new(Expression::Modifier(2)),
            value: Box::new(Expression::Die(20)),
            ranker: Ranker::Lowest(1),
        };
        assert_eq!(got, want);
    }

    #[test]
    fn stats_roll() {
        let got = dice_notation::expression("4d6kh3").unwrap();
        let want = Expression::Repeated {
            count: Box::new(Expression::Modifier(4)),
            value: Box::new(Expression::Die(6)),
            ranker: Ranker::Highest(3),
        };
        assert_eq!(got, want);
    }

    #[test]
    fn negative() {
        let got = dice_notation::expression("-4").unwrap();
        let want = Expression::Negated(Box::new(Expression::Modifier(4)));
        assert_eq!(got, want);
    }

    #[test]
    fn multiply() {
        let got = dice_notation::expression("4 * d6").unwrap();
        let want = Expression::Product(
            Box::new(Expression::Modifier(4)),
            Box::new(Expression::Die(6)),
        );
        assert_eq!(got, want);
    }

    #[test]
    fn sum() {
        let got = dice_notation::expression("d4 + d6").unwrap();
        let want = Expression::Sum(vec![Expression::Die(4), Expression::Die(6)]);
        assert_eq!(got, want);
    }

    #[test]
    fn compare() {
        let got = dice_notation::expression("d4 < d6").unwrap();
        let want = Expression::Comparison(
            Box::new(Expression::Die(4)),
            ComparisonOp::Lt,
            Box::new(Expression::Die(6)),
        );
        assert_eq!(got, want);
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
            let got = dice_notation::expression(&s).unwrap();
            assert_eq!(got.simplify(), exp.simplify());
        }
    }

    proptest! {
        #[test]
        fn expression_without_space(exp in recursive_expression()) {
            let s = exp.to_string();
            let s : String = s.chars().filter(|c| *c != ' ').collect();
            let got = dice_notation::expression(&s).unwrap();
            let got_simpl = got.clone().simplify();
            let want_simpl = exp.simplify();
            assert_eq!(got_simpl, want_simpl, "\n{got}\n{s}");
        }
    }
}
