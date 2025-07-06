//! Utilities for working with dice notation.

use discrete::Distributable;
use wasm_bindgen::prelude::*;

use dice_notation::expression;

mod reduced;
pub use reduced::ReducedExpression;

pub mod discrete;
// pub mod math;

/// Demo: parse, reduce, and canonicalize the dice expression.
#[wasm_bindgen]
pub fn canonicalize(input: &str) -> String {
    match expression(input) {
        Err(e) => format!("failed to parse: {e}"),
        Ok(v) => v.canonicalize().to_string(),
    }
}

/// Get the distribution of the expression as an HTML table.
#[wasm_bindgen]
pub fn distribution_table(input: &str) -> String {
    let e = match expression(input) {
        Err(e) => return maud::html!(p { "Error: " (e) }).into_string(),
        Ok(v) => v,
    };
    let r: ReducedExpression = e.into();
    r.distribution().html_table().into()
}

/// A roll of a number of dice of a given size: NdM.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(test, derive(proptest_derive::Arbitrary))]
struct Dice {
    n: usize,
    m: usize,
}

impl std::fmt::Display for Dice {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}d{}", self.n, self.m)
    }
}

/// A composite dice expression.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Expression {
    Roll(Dice),
    Modifier(usize),
    Negation(Box<Expression>),
    Sum(Vec<Expression>),
}

impl Expression {
    /// Reduce and canonicalize the expression.
    pub fn canonicalize(self) -> Expression {
        let reduced: ReducedExpression = self.into();
        reduced.into()
    }
}

impl std::fmt::Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Roll(dice) => dice.fmt(f),
            Expression::Modifier(n) => n.fmt(f),
            Expression::Negation(expr) => {
                // When printing a negation, we let atoms stay unparenthesized, but parenthesize
                // the rest.
                // Same rules as other hierarchical expressions.
                match &**expr {
                    Expression::Roll(_) | Expression::Modifier(_) => write!(f, "-{expr}"),
                    _ => write!(f, "-({expr})"),
                }
            }
            Expression::Sum(expressions) => {
                for (i, expr) in expressions.iter().enumerate() {
                    // When printing a negation in a sum, we substitute the negation's - for the
                    // sum's +.
                    let (operator, expr) = match (i, expr) {
                        (_, Expression::Negation(inner)) => (" - ", &**inner),
                        (0, e) => ("", e),
                        (_, e) => (" + ", e),
                    };
                    // Don't parenthesize if printing atoms (rolls and modifiers);
                    // but otherwise, parenthesize to make precedence explicit.
                    match expr {
                        Expression::Roll(_) | Expression::Modifier(_) => {
                            write!(f, "{operator}{expr}")?
                        }
                        _ => write!(f, "{operator}({expr})")?,
                    }
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

        pub(crate) rule dice() -> Dice
            = n:(number()) "d" m:(number()) { Dice{n, m} }

        rule modifier() -> usize
          = "+"? n:number() { n }

        rule paren_expr() -> Expression
            = "(" " "* exp:expression() " "* ")" { exp }

        rule simple_expression() -> Expression
            =   paren_expr()
            /   d:dice()    { Expression::Roll(d) }
            /   m:modifier()  { Expression::Modifier(m) }
            /   "-" " "* e:simple_expression() { Expression::Negation(Box::new(e)) }

        rule operator() -> char
            = " "* c:['+' | '-'] " "* { c }

        rule repeated_expression() -> Expression
            = op:operator() e:simple_expression() {
                if op == '-' {
                    Expression::Negation(Box::new(e))
                } else {
                    e
                }
            }

        rule sum_expression() -> Expression
            = car:simple_expression() cdr:repeated_expression()+ {
                let mut v = cdr;
                v.insert(0, car);
                Expression::Sum(v)
            }

        pub rule expression() -> Expression
            = " "* exp:(sum_expression() / simple_expression()) " "* { exp }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn formats() {
        for (want, dice) in [("1d4", Dice { n: 1, m: 4 }), ("2d20", Dice { n: 2, m: 20 })] {
            let got = dice.to_string();
            assert_eq!(&got, want);
        }
    }

    #[test]
    fn tetrahedron() {
        let d = dice_notation::dice("1d4").unwrap();
        assert_eq!(d, Dice { n: 1, m: 4 });
    }

    proptest! {
        #[test]
        fn dice_roundtrip(dice in any::<Dice>()) {
            let s = dice.to_string();
            let d = dice_notation::dice(&s).unwrap();
            assert_eq!(d, dice);
        }
    }

    #[test]
    fn simplifying_formats() {
        for (expand, simple) in [
            ("- ( - 1d4   )", "-(-1d4)"),
            ("1 - ( - 1d4   )", "1 - (-1d4)"),
            ("(2d20)", "2d20"),
            ("+5", "5"),
        ] {
            let Ok(d) = dice_notation::expression(expand) else {
                panic!("failed to parse \"{expand}\"")
            };
            let s = d.to_string();
            assert_eq!(&s, simple, "got: {} want: {}", &s, simple);
        }
    }

    #[test]
    fn roundtrip_neg_example() {
        let expr = Expression::Negation(Box::new(Expression::Negation(Box::new(
            Expression::Roll(Dice { n: 1, m: 4 }),
        ))));
        let s = expr.to_string();
        let simpl = expr;
        let got = dice_notation::expression(&s).unwrap();
        assert_eq!(got, simpl);
    }

    #[test]
    fn roundtrip_rolls_example() {
        let expr = Expression::Sum(vec![
            Expression::Roll(Dice { n: 0, m: 0 }),
            Expression::Roll(Dice { n: 0, m: 0 }),
        ]);
        let s = expr.to_string();
        let simpl = expr;
        let got = dice_notation::expression(&s).unwrap();
        assert_eq!(got, simpl);
    }

    /// Generate a possibly-recursive Expression.
    fn recursive_expression() -> impl Strategy<Value = Expression> {
        let leaf = proptest::prop_oneof![
            any::<Dice>().prop_map(Expression::Roll),
            any::<usize>().prop_map(Expression::Modifier),
        ];
        leaf.prop_recursive(3, 16, 3, |strat| {
            prop_oneof![
                strat
                    .clone()
                    .prop_map(|expr| Expression::Negation(Box::new(expr))),
                prop::collection::vec(strat, 2..10).prop_map(Expression::Sum),
            ]
        })
    }

    proptest! {
        #[test]
        fn expression_roundtrip(exp in recursive_expression()) {
            let s = exp.to_string();
            let got = dice_notation::expression(&s).unwrap();
            assert_eq!(got, exp);
        }
    }

    proptest! {
        #[test]
        fn expression_without_space(exp in recursive_expression()) {
            let s = exp.to_string();
            let s : String = s.chars().filter(|c| *c != ' ').collect();
            let got = dice_notation::expression(&s).unwrap();
            assert_eq!(got, exp);
        }
    }
}
