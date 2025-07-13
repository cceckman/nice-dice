//! The types and grammar for parsing dice expressions.

use std::str::FromStr;

use peg::{error::ParseError, str::LineCol};

use crate::{Error, symbolic::BindingAtom, symbolic::Constant, symbolic::Die};

type Expression = crate::symbolic::Expression<BindingAtom>;

peg::parser! {
    grammar dice_notation() for str {
        rule number() -> usize
          = n:$(['0'..='9']+) {? n.parse().or(Err("usize")) }

        rule die() -> Expression
            = "d" n:number() { Die(n).into() }

        rule modifier() -> Expression
            = n:number() { Constant(n).into() }

        rule symbol_token() -> Symbol
            = s:$(['a'..='z'|'A'..='Z']+) {? s.parse().or(Err("symbol")) }

        rule symbol_expr() -> Expression
            = s:symbol_token() { s.into() }

        rule binding() -> Expression
            = "[" space() symbol:symbol_token() space() ":" space() e:expression() space() "]" {
                Expression::Atom(BindingAtom::Binding{ symbol, expression: Box::new(e) })
            }

        rule paren() -> Expression
            = "(" space() e:expression() space() ")" { e }

        rule repeatable() -> Expression
            = paren() / die()

        rule repetitions() -> Expression
            = n:number() { Constant(n).into() }
            / paren()

        rule repeat() -> Expression
            = count:repetitions() space() expr:repeatable() rank:ranker()? {
                Expression::Repeated{count: Box::new(count), value: Box::new(expr), ranker: rank.unwrap_or(Ranker::All)} }

        rule ranker() -> Ranker
            = "kl" n:number()? { Ranker::Lowest(n.unwrap_or(1)) }
            / "kh" n:number()? { Ranker::Highest(n.unwrap_or(1)) }

        rule space() = quiet!{[' ' | '\n' | '\r' | '\t']*}

        rule pos_subterm() -> Expression
            = binding() / repeat() / die() / modifier() / symbol_expr() / paren()

        rule subterm() -> Expression
            = pos_subterm()
            /   "-" e:(pos_subterm()) { Expression::Negated(Box::new(e)) }

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

        rule comparison() -> Expression
            = space() a:sum() space() op:compare_op() space() b:sum()
        { Expression::Comparison{a:Box::new(a), b:Box::new(b),  op} }

        pub(crate) rule expression() -> Expression
            = comparison() / space() e:sum() space() { e }
    }
}

impl FromStr for Expression {
    type Err = ParseError<LineCol>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(dice_notation::expression(s)?.simplify())
    }
}

impl Expression {
    /// Simplify the expression, where possible.
    pub fn simplify(self) -> Self {
        match self {
            Expression::Atom(a) => match a {
                BindingAtom::Binding { symbol, expression } => BindingAtom::Binding {
                    symbol,
                    expression: Box::new(expression.simplify()),
                }
                .into(),
                other => other.into(),
            },
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
            Expression::Comparison { a, b, op } => {
                let a = Box::new(a.simplify());
                let b = Box::new(b.simplify());
                Expression::Comparison { a, b, op }
            }
        }
    }
}

/// Representing some portion of the expression.
/// Restricted to capital letters, A-Z.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(String);

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl FromStr for Symbol {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if let Some(c) = s.chars().find(|c| !c.is_ascii_uppercase()) {
            Err(Error::InvalidSymbolCharacter(c))
        } else {
            Ok(Symbol(s.to_owned()))
        }
    }
}

/// A ranking function: keep highest / keep lowest / keep all.
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
pub enum Ranker {
    All,
    Highest(usize),
    Lowest(usize),
}

impl Ranker {
    /// The minimum count of values required by this ranker.
    pub fn count(&self) -> usize {
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

/// A comparison operation (or the trivial comparison, which is always True)
#[derive(PartialEq, Eq, Debug, Clone, Copy)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
pub enum ComparisonOp {
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

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn sole_die() {
        let got: Expression = "d6".parse().unwrap();
        let want = Die(6).into();
        assert_eq!(got, want);
    }

    #[test]
    fn several_dice() {
        let got: Expression = "1d20".parse().unwrap();
        let want = Expression::Repeated {
            count: Box::new(Constant(1).into()),
            value: Box::new(Die(20).into()),
            ranker: Ranker::All,
        };
        assert_eq!(got, want);
    }

    #[test]
    fn modifier() {
        let got: Expression = "3".parse().unwrap();
        let want = Constant(3).into();
        assert_eq!(got, want);
    }

    #[test]
    fn multiply_chain() {
        let got: Expression = "3 * 4 * 5".parse().unwrap();
        let want = Expression::Product(
            Box::new(Constant(3).into()),
            Box::new(Expression::Product(
                Box::new(Constant(4).into()),
                Box::new(Constant(5).into()),
            )),
        );

        assert_eq!(got, want);
    }

    #[test]
    fn disadvantage() {
        let got: Expression = "2d20kl".parse().unwrap();
        let want = Expression::Repeated {
            count: Box::new(Constant(2).into()),
            value: Box::new(Die(20).into()),
            ranker: Ranker::Lowest(1),
        };
        assert_eq!(got, want);
    }

    #[test]
    fn stats_roll() {
        let got: Expression = "4d6kh3".parse().unwrap();
        let want = Expression::Repeated {
            count: Box::new(Constant(4).into()),
            value: Box::new(Die(6).into()),
            ranker: Ranker::Highest(3),
        };
        assert_eq!(got, want);
    }

    #[test]
    fn negative() {
        let got: Expression = "-4".parse().unwrap();
        let want = Expression::Negated(Box::new(Constant(4).into()));
        assert_eq!(got, want);
    }

    #[test]
    fn multiply() {
        let got: Expression = "4 * d6".parse().unwrap();
        let want = Expression::Product(Box::new(Constant(4).into()), Box::new(Die(6).into()));
        assert_eq!(got, want);
    }

    #[test]
    fn sum() {
        let got: Expression = "d4 + d6".parse().unwrap();
        let want = Expression::Sum(vec![Die(4).into(), Die(6).into()]);
        assert_eq!(got, want);
    }

    #[test]
    fn compare() {
        let got: Expression = "(d4 <= 3)".parse().unwrap();
        let want = Expression::Comparison {
            a: Box::new(Die(4).into()),
            b: Box::new(Constant(3).into()),
            op: ComparisonOp::Le,
        };
        assert_eq!(got, want);
    }

    fn symbol() -> impl Strategy<Value = Symbol> {
        proptest::string::string_regex("[A-Z]+")
            .expect("valid regex")
            .prop_map(|s| s.parse().unwrap())
    }

    /// Generate a possibly-recursive Expression.
    fn recursive_expression() -> impl Strategy<Value = Expression> {
        let leaf = proptest::prop_oneof![
            any::<usize>().prop_map(|v| Die(v).into()),
            any::<usize>().prop_map(|v| Constant(v).into()),
            symbol().prop_map(|s| s.into()),
        ];
        leaf.prop_recursive(3, 2, 3, |strat| {
            prop_oneof![
                // Repetition:
                (strat.clone(), strat.clone(), any::<Ranker>()).prop_map(
                    |(count, value, ranker)| Expression::Repeated {
                        count: Box::new(count),
                        value: Box::new(value),
                        ranker
                    }
                ),
                // Product:
                (strat.clone(), strat.clone())
                    .prop_map(|(a, b)| { Expression::Product(Box::new(a), Box::new(b)) }),
                // Division:
                (strat.clone(), strat.clone())
                    .prop_map(|(a, b)| { Expression::Floor(Box::new(a), Box::new(b)) }),
                // Sum:
                prop::collection::vec(strat.clone(), 2..5).prop_map(Expression::Sum),
                // Comparison:
                (strat.clone(), strat.clone(), any::<ComparisonOp>()).prop_map(|(a, b, op)| {
                    Expression::Comparison {
                        a: Box::new(a),
                        b: Box::new(b),
                        op,
                    }
                }),
                // Binding:
                (symbol(), strat.clone()).prop_map(|(symbol, expression)| BindingAtom::Binding {
                    symbol,
                    expression: Box::new(expression)
                }
                .into()),
            ]
        })
    }

    proptest! {
        #[test]
        fn expression_roundtrip(exp in recursive_expression()) {
            let s = exp.to_string();
            let got: Expression = s.parse().map_err(|e| {
                TestCaseError::fail(format!("expression: {s}\n{e}"))
            })?;
            assert_eq!(got.simplify(), exp.simplify(), "expression: {s}");
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
