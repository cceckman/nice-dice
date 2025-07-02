use std::collections::{BTreeMap, VecDeque};

use crate::{Dice, Expression};

/// A dice expresion in reduced form.
///
/// Reduction:
/// - The expression is flattened: parentheses are stripped and negations distributed.
/// - Positive and negative modifiers are combined (summed).
/// - Positive (adding) dice are combined with positive dice of the same size.
/// - Negative (subtracting) dice are combined with negative dice of the same size.
/// - Zero terms (0dXX, Nd0) are removed.
///
/// A reduced expression does not preserve order of terms.
///
/// When converted to an Expression, the resulting expression is _canonical_:
/// Terms are ordered by decreasing die size, and by positive then negative within a size;
/// e.g. `2d20 - 1d20 + 5d10 - 7d10 + 1`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct ReducedExpression {
    positives: BTreeMap<usize, usize>,
    negatives: BTreeMap<usize, usize>,
    modifier: isize,
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

impl std::fmt::Display for ReducedExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let e: Expression = self.clone().into();
        e.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use crate::dice_notation;

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
}
