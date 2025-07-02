//! Utilities for working with dice notation.

use std::collections::{BTreeMap, VecDeque};

use wasm_bindgen::prelude::*;

use dice_notation::expression;

/// Demo: parse, reduce, and canonicalize the dice expression.
#[wasm_bindgen]
pub fn canonicalize(input: &str) -> String {
    match expression(input) {
        Err(e) => format!("failed to parse: {e}"),
        Ok(v) => v.canonicalize().to_string(),
    }
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
    /// Lexically simplify the expression.
    fn simplify(self) -> Expression {
        match self {
            Expression::Roll(_) => self,
            Expression::Modifier(_) => self,
            Expression::Negation(expression) => {
                match expression.simplify() {
                    Expression::Negation(expression) =>
                    // Double-negative; unwrap.
                    {
                        *expression
                    }
                    e => Expression::Negation(Box::new(e)),
                }
            }
            Expression::Sum(mut expressions) => {
                if expressions.len() == 1 {
                    expressions.pop().unwrap().simplify()
                } else {
                    Expression::Sum(expressions.into_iter().map(|e| e.simplify()).collect())
                }
            }
        }
    }

    /// Reduce and canonicalize the expression.
    ///
    /// Reduction:
    /// - The expression is flattened: parentheses are stripped and negations distributed.
    /// - Positive and negative modifiers are combined (summed).
    /// - Positive (adding) dice are combined with positive dice of the same size.
    /// - Negative (subtracting) dice are combined with negative dice of the same size.
    ///
    /// Note that positive and negative dice are not combined _with each other_.
    /// The distribution of `1d20 - 1d20` is not the same as the distribution of `0d20`.
    ///
    /// Canonicalization:
    /// Terms are ordered by decreasing die size, and by positive then negative within a size;
    /// e.g. `2d20 - 1d20 + 5d10 - 7d10 + 1`.
    pub fn canonicalize(self) -> Expression {
        // Positive and negative dice, accumulated.
        let mut positives: BTreeMap<usize, usize> = Default::default();
        let mut negatives: BTreeMap<usize, usize> = Default::default();
        let mut modifier: isize = 0;

        let mut queue: VecDeque<Expression> = [self].into_iter().collect();
        while let Some(e) = queue.pop_front() {
            match e {
                Expression::Roll(Dice { n, m }) => {
                    *positives.entry(m).or_default() += n;
                }
                Expression::Modifier(n) => modifier += n as isize,
                Expression::Sum(expressions) => queue.extend(expressions),
                Expression::Negation(boxed) => {
                    match *boxed {
                        // Double-negative becomes just the positive.
                        Expression::Negation(expression) => queue.push_front(*expression),
                        // Distribute the negation across all the sub-expressions.
                        Expression::Sum(expressions) => queue.extend(
                            expressions
                                .into_iter()
                                .map(|v| Expression::Negation(Box::new(v))),
                        ),
                        Expression::Roll(Dice { n, m }) => *negatives.entry(m).or_default() += n,
                        Expression::Modifier(n) => modifier -= n as isize,
                    }
                }
            }
        }

        let mut expressions = Vec::new();

        {
            fn make_dice((&m, &n): (&usize, &usize)) -> Option<Dice> {
                if m > 0 && n > 0 {
                    Some(Dice { n, m })
                } else {
                    None
                }
            }

            let mut positives = positives.iter().rev().filter_map(make_dice);
            let mut negatives = negatives.iter().rev().filter_map(make_dice);
            // Manually zip, maintaining largest to smallest die order.
            let mut next_pos = positives.next();
            let mut next_neg = negatives.next();

            while let (Some(pos), Some(neg)) = (next_pos, next_neg) {
                if neg.m > pos.m {
                    expressions.push(Expression::Negation(Box::new(Expression::Roll(neg))));
                    next_neg = negatives.next();
                    continue;
                } else {
                    expressions.push(Expression::Roll(pos));
                    next_pos = positives.next();
                    continue;
                }
            }
            // At the end of the above loop, at least one of "positives" or "negatives" is exhausted.
            if let Some(pos) = next_pos {
                expressions.push(Expression::Roll(pos));
                expressions.extend(positives.map(Expression::Roll))
            }
            if let Some(neg) = next_neg {
                expressions.push(Expression::Negation(Box::new(Expression::Roll(neg))));
                expressions.extend(
                    negatives.map(|neg| Expression::Negation(Box::new(Expression::Roll(neg)))),
                );
            }
        }
        if modifier < 0 {
            expressions.push(Expression::Negation(Box::new(Expression::Modifier(
                modifier.unsigned_abs(),
            ))));
        } else if modifier > 0 {
            expressions.push(Expression::Modifier(modifier as usize));
        }

        match expressions.len() {
            0 => Expression::Modifier(0),
            1 => expressions.pop().unwrap(),
            _ => Expression::Sum(expressions),
        }
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
    fn canonicalize() {
        for (expand, simple) in [
            ("4 - 1", "3"),
            ("1d20 + 1d20", "2d20"),
            ("4 + 1d4 - 3 + (2d20 + 5) + 1d20", "3d20 + 1d4 + 6"),
            ("1d4 - (1d4 - (1d4 + 3))", "2d4 - 1d4 + 3"),
        ] {
            let Ok(d) = dice_notation::expression(expand) else {
                panic!("failed to parse \"{expand}\"")
            };
            let d = d.canonicalize();
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
