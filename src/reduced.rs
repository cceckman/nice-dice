use std::collections::{BTreeMap, VecDeque};

use crate::{Dice, Expression, analysis::Analytic};

/// A dice expresion in reduced and canonicalized form.
///
/// Reduction:
/// - The expression is flattened: parentheses are stripped and negations distributed.
/// - Positive and negative modifiers are combined (summed).
/// - Positive (adding) dice are combined with positive dice of the same size.
/// - Negative (subtracting) dice are combined with negative dice of the same size.
/// - Zero terms (0dXX, Nd0) are removed.
///
/// The reduced expression does not preserve the order of terms.
///
/// When converted to an Expression, the resulting expression is _canonical_:
/// Terms are ordered by decreasing die size, and by positive then negative within a size;
/// e.g. `2d20 - 1d20 + 5d10 - 7d10 + 1`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ReducedExpression {
    positives: Vec<Dice>,
    negatives: Vec<Dice>,
    modifier: isize,
}

/// Map the dice by the provided optional-generating function.
/// Return Some(sum of the mappings) if all are Some, or return None (short-circuit).
fn optional_summation<'a>(
    l: impl Iterator<Item = &'a Dice>,
    f: impl FnMut(&Dice) -> Option<isize>,
) -> Option<isize> {
    l.map(f)
        .reduce(|a, b| {
            let a = a?;
            let b = b?;
            Some(a + b)
        })
        // The outer Optional<> indicates an empty list; that's fine.
        // The inner Optional<> indicates an expression without a maximum;
        // that means we need to return "unbounded" too.
        .unwrap_or(Some(0))
}
impl Analytic for ReducedExpression {
    fn max(&self) -> Option<isize> {
        let positive = optional_summation(self.positives.iter(), Dice::max)?;
        let negative = optional_summation(self.negatives.iter(), Dice::min)?;
        Some(positive - negative + self.modifier)
    }

    fn min(&self) -> Option<isize> {
        let positive = optional_summation(self.positives.iter(), Dice::min)?;
        let negative = optional_summation(self.negatives.iter(), Dice::max)?;
        Some(positive - negative + self.modifier)
    }

    fn expected_value(&self) -> f32 {
        let positive: f32 = self.positives.iter().map(|v| v.expected_value()).sum();
        let negative: f32 = self.negatives.iter().map(|v| v.expected_value()).sum();
        positive - negative + (self.modifier as f32)
    }
}

impl From<Expression> for ReducedExpression {
    fn from(value: Expression) -> Self {
        // Positive and negative dice, accumulated.
        let mut positives: BTreeMap<usize, usize> = Default::default();
        let mut negatives: BTreeMap<usize, usize> = Default::default();
        let mut modifier: isize = 0;

        let mut queue: VecDeque<Expression> = [value].into_iter().collect();
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
        fn make_dice((m, n): (usize, usize)) -> Option<Dice> {
            if m > 0 && n > 0 {
                Some(Dice { n, m })
            } else {
                None
            }
        }

        let positives = positives.into_iter().rev().filter_map(make_dice).collect();
        let negatives = negatives.into_iter().rev().filter_map(make_dice).collect();

        ReducedExpression {
            positives,
            negatives,
            modifier,
        }
    }
}

impl From<ReducedExpression> for Expression {
    fn from(value: ReducedExpression) -> Self {
        let ReducedExpression {
            positives,
            negatives,
            modifier,
        } = value;
        let mut expressions = Vec::new();

        {
            let mut positives = positives.into_iter();
            let mut negatives = negatives.into_iter();
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

impl std::fmt::Display for ReducedExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let e: Expression = self.clone().into();
        e.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use crate::{analysis::Analytic, dice_notation};

    use super::ReducedExpression;

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
    fn max() {
        for (expr, want) in [("1d20+1", Some(21)), ("1d20-1d20", Some(19))] {
            let canon: ReducedExpression = dice_notation::expression(expr)
                .expect("could not parse expression")
                .into();
            let got = canon.max();

            assert_eq!(got, want, "for expression: {expr} canon: {canon}");
        }
    }

    #[test]
    fn min() {
        for (expr, want) in [("1d20+1", Some(2)), ("1d20-1d20", Some(-19))] {
            let canon: ReducedExpression = dice_notation::expression(expr)
                .expect("could not parse expression")
                .into();
            let got = canon.min();

            assert_eq!(got, want, "for expression: {expr} canon: {canon}");
        }
    }

    #[test]
    fn expected_value() {
        for (expr, want_ev) in [("1d20+1", 11.5), ("1d20-1d20", 0.0)] {
            let canon: ReducedExpression = dice_notation::expression(expr)
                .expect("could not parse expression")
                .into();
            let got_ev = canon.expected_value();
            let diff = (got_ev - want_ev).abs();

            assert!(
                diff < 0.00001,
                "got: {got_ev} want: {want_ev} for: {expr} canon: {canon}"
            )
        }
    }
}
