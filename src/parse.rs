//! The types and grammar for parsing dice expressions.

use std::str::FromStr;

use crate::symbolic::*;

type ExpressionTree = crate::symbolic::ExpressionTree<RawExpression>;

peg::parser! {
    grammar dice_notation() for str {
        rule number() -> usize
          = n:$(['0'..='9']+) {? n.parse().or(Err("usize")) }

        rule die() -> RawExpression
            = "d" n:number() { Die(n).into() }

        rule modifier() -> RawExpression
            = "+"? n:number() { Constant(n).into() }

        rule symbol_token() -> Symbol
            = s:$(['a'..='z'|'A'..='Z']+) {? s.parse().or(Err("symbol")) }

        rule symbol_expr() -> RawExpression
            = s:symbol_token() { s.into() }

        rule paren() -> RawExpression
            = "(" space() e:expression() space() ")" { e }

        rule repeatable() -> RawExpression
            = paren() / die()

        rule repetitions() -> RawExpression
            = n:number() { Constant(n).into() }
            / paren()

        rule repeat() -> RawExpression
            = count:repetitions() space() expr:repeatable() rank:ranker()? {
                ExpressionTree::Repeated{count: Box::new(count), value: Box::new(expr), ranker: rank.unwrap_or(Ranker::All)}.into() }

        rule ranker() -> Ranker
            = "kl" n:number()? { Ranker::Lowest(n.unwrap_or(1)) }
            / "kh" n:number()? { Ranker::Highest(n.unwrap_or(1)) }

        rule space() = quiet!{[' ' | '\n' | '\r' | '\t']*}

        rule pos_subterm() -> RawExpression
            = repeat() / die() / modifier() / symbol_expr() / paren()

        rule subterm() -> RawExpression
            = pos_subterm()
            /   "-" e:(pos_subterm()) { ExpressionTree::Negated(Box::new(e)).into() }

        rule term() -> RawExpression
            = e1:subterm() space() "*" space() e2:term() { ExpressionTree::Product(Box::new(e1), Box::new(e2)).into() }
            / e1:subterm() space() "/" space() e2:term() { ExpressionTree::Floor(Box::new(e1), Box::new(e2)).into() }
            // e1:subterm() space() "/^" space() e2:subterm() { Expression::Ceiling(e1, e2) }
            / subterm()

        rule sum_tail() -> RawExpression
            = space() "-" space() e2:term() { ExpressionTree::Negated(Box::new(e2)).into() }
            / space() "+" space() e2:term() { e2 }

        rule sum() -> RawExpression
            = e1:term() e2:sum_tail()+ { ExpressionTree::Sum(std::iter::once(e1).chain(e2.into_iter()).collect()).into() }
            / term()

        rule compare_op() -> ComparisonOp
            // Note: order matters! Match the longer >= sequences first.
            = (">=" / "≥") { ComparisonOp::Ge }
            / ">" { ComparisonOp::Gt }
            / "=" { ComparisonOp::Eq }
            / ("<=" / "≤") { ComparisonOp::Le }
            / "<" { ComparisonOp::Lt }

        rule compare_term() -> RawExpression
            = sum() / paren()

        rule comparison() -> RawExpression
            = space() a:compare_term() space() op:compare_op() space() b:compare_term()
        { ExpressionTree::Comparison{a:Box::new(a), b:Box::new(b),  op}.into() }

        rule symbolic_expression() -> RawExpression
            = comparison() / space() e:sum() space() { e }

        rule binding() -> RawExpression
            = "[" space() symbol:symbol_token() space() ":" e:expression() "]" tail:expression() {
                ExpressionTree::Binding{symbol, value: Box::new(e), tail: Box::new(tail) }.into()
            } / symbolic_expression()

        pub(crate) rule expression() -> RawExpression
            = space() e:binding() space() { e }
    }
}

/// An expression tree that has not been semantically analyzed.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct RawExpression(ExpressionTree);

impl ExpressionWrapper for RawExpression {
    fn inner(&self) -> &crate::symbolic::ExpressionTree<Self> {
        &self.0
    }
}

impl std::fmt::Display for RawExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl FromStr for RawExpression {
    type Err = crate::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(dice_notation::expression(s)
            .map_err(|e| crate::Error::ParseError(s.to_owned(), e))?
            .simplify())
    }
}

impl<T> From<T> for RawExpression
where
    T: Into<ExpressionTree>,
{
    fn from(value: T) -> Self {
        let tree = value.into();
        RawExpression(tree)
    }
}

impl RawExpression {
    /// Simplify the expression, where possible.
    pub fn simplify(self) -> Self {
        match self.0 {
            ExpressionTree::Modifier(_) => self,
            ExpressionTree::Die(_) => self,
            ExpressionTree::Symbol(_) => self,
            ExpressionTree::Negated(inner) => {
                let simpl = inner.simplify();
                match simpl.0 {
                    ExpressionTree::Negated(e) => *e,
                    _ => ExpressionTree::Negated(Box::new(simpl)).into(),
                }
            }
            ExpressionTree::Repeated {
                count,
                value,
                ranker,
            } => ExpressionTree::Repeated {
                count: Box::new(count.simplify()),
                value: Box::new(value.simplify()),
                ranker,
            }
            .into(),
            ExpressionTree::Product(a, b) => {
                ExpressionTree::Product(Box::new(a.simplify()), Box::new(b.simplify())).into()
            }
            ExpressionTree::Floor(a, b) => {
                ExpressionTree::Floor(Box::new(a.simplify()), Box::new(b.simplify())).into()
            }
            ExpressionTree::Sum(expressions) => {
                let mut es = Vec::new();
                for e in expressions.into_iter() {
                    let e = e.simplify();
                    if let ExpressionTree::Sum(inner) = e.0 {
                        es.extend(inner)
                    } else {
                        es.push(e)
                    };
                }
                if es.len() == 1 {
                    es.pop().unwrap()
                } else {
                    RawExpression(ExpressionTree::Sum(es))
                }
            }
            ExpressionTree::Comparison { a, b, op } => {
                let a = Box::new(a.simplify());
                let b = Box::new(b.simplify());
                ExpressionTree::Comparison { a, b, op }.into()
            }
            ExpressionTree::Binding {
                symbol,
                value,
                tail,
            } => {
                let value = Box::new(value.simplify());
                let tail = Box::new(tail.simplify());
                ExpressionTree::Binding {
                    symbol,
                    value,
                    tail,
                }
                .into()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn sole_die() {
        let got: RawExpression = "d6".parse().unwrap();
        let want = Die(6).into();
        assert_eq!(got, want);
    }

    #[test]
    fn several_dice() {
        let got: RawExpression = "1d20".parse().unwrap();
        let want = ExpressionTree::Repeated {
            count: Box::new(Constant(1).into()),
            value: Box::new(Die(20).into()),
            ranker: Ranker::All,
        }
        .into();
        assert_eq!(got, want);
    }

    #[test]
    fn modifier() {
        let got: RawExpression = "3".parse().unwrap();
        let want = Constant(3).into();
        assert_eq!(got, want);
    }

    #[test]
    fn multiply_chain() {
        let got: RawExpression = "3 * 4 * 5".parse().unwrap();
        let want = ExpressionTree::Product(
            Box::new(Constant(3).into()),
            Box::new(
                ExpressionTree::Product(Box::new(Constant(4).into()), Box::new(Constant(5).into()))
                    .into(),
            ),
        )
        .into();

        assert_eq!(got, want);
    }

    #[test]
    fn disadvantage() {
        let got: RawExpression = "2d20kl".parse().unwrap();
        let want = ExpressionTree::Repeated {
            count: Box::new(Constant(2).into()),
            value: Box::new(Die(20).into()),
            ranker: Ranker::Lowest(1),
        };
        assert_eq!(got, want.into());
    }

    #[test]
    fn stats_roll() {
        let got: RawExpression = "4d6kh3".parse().unwrap();
        let want = ExpressionTree::Repeated {
            count: Box::new(Constant(4).into()),
            value: Box::new(Die(6).into()),
            ranker: Ranker::Highest(3),
        };
        assert_eq!(got, want.into());
    }

    #[test]
    fn negative() {
        let got: RawExpression = "-4".parse().unwrap();
        let want = ExpressionTree::Negated(Box::new(Constant(4).into()));
        assert_eq!(got, want.into());
    }

    #[test]
    fn multiply() {
        let got: RawExpression = "4 * d6".parse().unwrap();
        let want = ExpressionTree::Product(Box::new(Constant(4).into()), Box::new(Die(6).into()));
        assert_eq!(got, want.into());
    }

    #[test]
    fn sum() {
        let got: RawExpression = "d4 + d6".parse().unwrap();
        let want = ExpressionTree::Sum(vec![Die(4).into(), Die(6).into()]);
        assert_eq!(got, want.into());
    }

    #[test]
    fn compare() {
        let got: RawExpression = "(d4 <= 3)".parse().unwrap();
        let want = ExpressionTree::Comparison {
            a: Box::new(Die(4).into()),
            b: Box::new(Constant(3).into()),
            op: ComparisonOp::Le,
        }
        .into();
        assert_eq!(got, want);
    }

    #[test]
    fn explicit_modifier_sign() {
        for (i, e) in ["[CHA: +2] CHA", "+3", "-3", "1 - +3", "1 + -+3", "-+3"]
            .into_iter()
            .enumerate()
        {
            let _: RawExpression = e.parse().unwrap_or_else(|_| panic!("case {i} failed"));
        }
    }

    fn symbol() -> impl Strategy<Value = Symbol> {
        proptest::string::string_regex("[A-Z]+")
            .expect("valid regex")
            .prop_map(|s| s.parse().unwrap())
    }

    /// Generate a symbolic Expression.
    /// Note: cannot contain Bindings.
    fn symbolic_expression() -> impl Strategy<Value = RawExpression> {
        let leaf = proptest::prop_oneof![
            any::<usize>().prop_map(|v| Die(v).into()),
            any::<usize>().prop_map(|v| Constant(v).into()),
            symbol().prop_map(|s| s.into()),
        ];
        leaf.prop_recursive(3, 2, 3, |strat| {
            prop_oneof![
                // Negation:
                strat
                    .clone()
                    .prop_map(|v| ExpressionTree::Negated(Box::new(v))),
                // Repetition:
                (strat.clone(), strat.clone(), any::<Ranker>()).prop_map(
                    |(count, value, ranker)| ExpressionTree::Repeated {
                        count: Box::new(count),
                        value: Box::new(value),
                        ranker
                    }
                ),
                // Product:
                (strat.clone(), strat.clone())
                    .prop_map(|(a, b)| { ExpressionTree::Product(Box::new(a), Box::new(b)) }),
                // Division:
                (strat.clone(), strat.clone())
                    .prop_map(|(a, b)| { ExpressionTree::Floor(Box::new(a), Box::new(b)) }),
                // Sum:
                prop::collection::vec(strat.clone(), 2..5).prop_map(ExpressionTree::Sum),
                // Comparison:
                (strat.clone(), strat.clone(), any::<ComparisonOp>()).prop_map(|(a, b, op)| {
                    ExpressionTree::Comparison {
                        a: Box::new(a),
                        b: Box::new(b),
                        op,
                    }
                }),
                // Binding:
                (symbol(), strat.clone(), strat.clone()).prop_map(|(symbol, value, tail)| {
                    ExpressionTree::Binding {
                        symbol,
                        value: Box::new(value),
                        tail: Box::new(tail),
                    }
                }),
            ]
            .prop_map(|v| v.into())
        })
    }

    proptest! {
        #[test]
        fn expression_roundtrip(exp in symbolic_expression()) {
            let s = exp.to_string();
            let got: RawExpression = s.parse().map_err(|e| {
                TestCaseError::fail(format!("expression: {s}\n{e}"))
            })?;
            assert_eq!(got.simplify(), exp.simplify(), "expression: {s}");
        }
    }

    proptest! {
        #[test]
        fn expression_without_space(exp in symbolic_expression()) {
            let s = exp.to_string();
            let s : String = s.chars().filter(|c| *c != ' ').collect();
            let got: RawExpression = s.parse().unwrap();
            let got_simpl = got.clone().simplify();
            let want_simpl = exp.simplify();
            assert_eq!(got_simpl, want_simpl, "\n{got}\n{s}");
        }
    }
}
