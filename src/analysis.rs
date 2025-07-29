//! Well-formedness checking (semantic analysis) of dice expressions.
//!
//! We need to make sure:
//! - All symbols are defined when used.
//! - Symbols do not conflict.
//! - Keep-highest / keep-lowest are always valid
//! - Division never divides by zero
//!

use std::str::FromStr;

use crate::{
    Error,
    parse::RawExpression,
    symbolic::{Constant, Die, ExpressionTree, ExpressionWrapper, Symbol},
};

/// An dice expression that is well-formed per semantic analysis.
///
/// - All symbols are declared before use, in the context of their use.
/// -
#[derive(Debug)]
pub struct WellFormed(ExpressionTree<WellFormed>);

impl WellFormed {
    /// The minimum value of this expression.
    pub fn minimum(&self) -> isize {
        self.min(&AvailableBinding::Root)
    }

    /// The maximum value of this expression.
    pub fn maximum(&self) -> isize {
        self.max(&AvailableBinding::Root)
    }
}

impl FromStr for WellFormed {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self, Error> {
        let v: RawExpression = s.parse()?;
        v.try_into()
    }
}

impl TryFrom<RawExpression> for WellFormed {
    type Error = Error;

    fn try_from(value: RawExpression) -> Result<Self, Self::Error> {
        WellFormed::check(&value, &AvailableBinding::Root)
    }
}

impl ExpressionWrapper for WellFormed {
    fn inner(&self) -> &ExpressionTree<Self> {
        &self.0
    }
}

impl std::fmt::Display for WellFormed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// Linked list (on the stack) of current symbol bindings.
#[derive(Copy, Clone)]
enum AvailableBinding<'a> {
    Root,
    Chain {
        defined: &'a Symbol,
        definition: &'a WellFormed,
        prev: &'a AvailableBinding<'a>,
    },
}

impl AvailableBinding<'_> {
    /// Search the stack of bindings for the provided symbol.
    fn search(&self, needle: &Symbol) -> Option<&WellFormed> {
        let mut current: &AvailableBinding = self;
        while let AvailableBinding::Chain {
            defined,
            prev,
            definition,
        } = current
        {
            if *defined == needle {
                return Some(definition);
            } else {
                current = prev;
            }
        }
        None
    }
}

impl WellFormed {
    fn max(&self, symbols: &AvailableBinding) -> isize {
        match self.inner() {
            ExpressionTree::Modifier(Constant(m)) => *m as isize,
            ExpressionTree::Die(Die(d)) => *d as isize,
            ExpressionTree::Symbol(symbol) => {
                let v = symbols
                    .search(symbol)
                    .expect("well-formed expression may only resolve defined symbols");
                v.max(symbols)
            }
            ExpressionTree::Negated(x) => -x.min(symbols),
            ExpressionTree::Repeated {
                count,
                value,
                ranker,
            } => {
                let max_count = count.max(symbols);
                let max_value = value.max(symbols);
                let count = std::cmp::min(ranker.count() as isize, max_count);
                count * max_value
            }
            ExpressionTree::Product(a, b) => {
                let (a_min, b_min) = (a.min(symbols), b.min(symbols));
                let (a_max, b_max) = (a.max(symbols), b.max(symbols));
                // I haven't though of a better way to handle the signs than brute-forcing.
                [a_min * b_min, a_max * b_max, a_min * b_max, a_max * b_min]
                    .iter()
                    .fold(isize::MIN, |a, &b| std::cmp::max(a, b))
            }
            ExpressionTree::Sum(items) => items.iter().map(|v| v.max(symbols)).sum(),
            ExpressionTree::Floor(a, b) => {
                let (a_min, b_min) = (a.min(symbols), b.min(symbols));
                let (a_max, b_max) = (a.max(symbols), b.max(symbols));
                // I haven't though of a better way to handle the signs than brute-forcing.
                [
                    a_min.checked_div(b_min),
                    a_max.checked_div(b_max),
                    a_max.checked_div(b_min),
                    a_min.checked_div(b_max),
                ]
                .iter()
                .filter_map(|v| *v)
                .fold(isize::MIN, std::cmp::max)
            }
            ExpressionTree::Comparison { .. } => {
                // TODO: : could short-circuit on irrefutable comparison.
                // For now, we assume every condition could be true or false.
                1
            }
            ExpressionTree::Binding {
                symbol,
                value,
                tail,
            } => {
                // We don't know if "min" or "max" gives us the max of the underlying expression.
                // Try both.
                // (All the operators we have are linear.... I think?)
                [value.max(symbols), value.min(symbols)]
                    .map(|v| {
                        // For the (minimum, maximum) value of this symbol,
                        // encode it as a constant to evaluate this expression.
                        let constant =
                            WellFormed(ExpressionTree::Modifier(Constant(v.unsigned_abs())));
                        let definition = if v >= 0 {
                            constant
                        } else {
                            WellFormed(ExpressionTree::Negated(Box::new(constant)))
                        };

                        let binding = AvailableBinding::Chain {
                            defined: symbol,
                            definition: &definition,
                            prev: symbols,
                        };

                        tail.max(&binding)
                    })
                    .iter()
                    .fold(isize::MIN, |a, b| std::cmp::max(a, *b))
            }
        }
    }

    /// Return the minimum possible value that can be generated by this expression.
    fn min(&self, symbols: &AvailableBinding) -> isize {
        match self.inner() {
            ExpressionTree::Modifier(Constant(m)) => *m as isize,
            ExpressionTree::Die(Die(_)) => 1,
            ExpressionTree::Symbol(symbol) => {
                let v = symbols
                    .search(symbol)
                    .expect("well-formed expression may only resolve defined symbols");
                v.min(symbols)
            }
            ExpressionTree::Negated(x) => -x.max(symbols),
            ExpressionTree::Repeated {
                count,
                value,
                ranker,
            } => {
                let max_count = count.min(symbols);
                let max_value = value.min(symbols);
                let count = std::cmp::min(ranker.count() as isize, max_count);
                count * max_value
            }
            ExpressionTree::Product(a, b) => {
                let (a_min, b_min) = (a.min(symbols), b.min(symbols));
                let (a_max, b_max) = (a.max(symbols), b.max(symbols));
                // I haven't though of a better way to handle the signs than brute-forcing.
                [a_min * b_min, a_max * b_max, a_min * b_max, a_max * b_min]
                    .iter()
                    .fold(isize::MAX, |a, &b| std::cmp::min(a, b))
            }
            ExpressionTree::Sum(items) => {
                // This handles sign correctly.
                items.iter().map(|v| v.min(symbols)).sum()
            }
            ExpressionTree::Floor(a, b) => {
                let (a_min, b_min) = (a.min(symbols), b.min(symbols));
                let (a_max, b_max) = (a.max(symbols), b.max(symbols));
                // I haven't though of a better way to handle the signs than brute-forcing.
                [
                    a_min.checked_div(b_min),
                    a_max.checked_div(b_max),
                    a_max.checked_div(b_min),
                    a_min.checked_div(b_max),
                ]
                .iter()
                .filter_map(|v| *v)
                .fold(isize::MAX, std::cmp::min)
            }
            ExpressionTree::Comparison { .. } => {
                // TODO: : could short-circuit on refutable comparison.
                // For now, we assume every condition could be true or false.
                0
            }
            ExpressionTree::Binding {
                symbol,
                value,
                tail,
            } => {
                // We don't know if "min" or "max" gives us the max of the underlying expression.
                // Try both.
                // (All the operators we have are linear.... I think?)
                [value.max(symbols), value.min(symbols)]
                    .map(|v| {
                        let constant =
                            WellFormed(ExpressionTree::Modifier(Constant(v.unsigned_abs())));
                        let definition = if v >= 0 {
                            constant
                        } else {
                            WellFormed(ExpressionTree::Negated(Box::new(constant)))
                        };

                        let binding = AvailableBinding::Chain {
                            defined: symbol,
                            definition: &definition,
                            prev: symbols,
                        };

                        tail.min(&binding)
                    })
                    .iter()
                    .fold(isize::MAX, |a, b| std::cmp::min(a, *b))
            }
        }
    }
}

impl WellFormed {
    /// Recursively check that this expression is well-formed, given the provided stack of
    /// bindings.
    fn check(target: &RawExpression, symbols: &AvailableBinding) -> Result<WellFormed, Error> {
        let tree: Result<ExpressionTree<WellFormed>, _> = match target.inner() {
            ExpressionTree::Modifier(m) => Ok(ExpressionTree::Modifier(*m)),
            ExpressionTree::Die(Die(d)) => {
                if *d == 0 {
                    Err(Error::ZeroFacedDie())
                } else {
                    Ok(ExpressionTree::Die(Die(*d)))
                }
            }
            ExpressionTree::Symbol(symbol) => {
                if symbols.search(symbol).is_some() {
                    Ok(ExpressionTree::Symbol(symbol.to_owned()))
                } else {
                    Err(Error::SymbolUndefined(symbol.to_owned()))
                }
            }
            ExpressionTree::Negated(n) => {
                let n = WellFormed::check(n, symbols)?;
                Ok(ExpressionTree::Negated(Box::new(n)))
            }
            ExpressionTree::Repeated {
                count,
                value,
                ranker,
            } => {
                let count = Box::new(WellFormed::check(count, symbols)?);
                let value = Box::new(WellFormed::check(value, symbols)?);

                let min_count = count.min(symbols);
                if min_count < (ranker.count() as isize) {
                    Err(crate::Error::KeepTooFew(ranker.count(), count.to_string()))
                } else {
                    Ok(ExpressionTree::Repeated {
                        count,
                        value,
                        ranker: *ranker,
                    })
                }
            }
            ExpressionTree::Product(a, b) => {
                let a = Box::new(WellFormed::check(a, symbols)?);
                let b = Box::new(WellFormed::check(b, symbols)?);
                Ok(ExpressionTree::Product(a, b))
            }
            ExpressionTree::Sum(expression_trees) => {
                let r: Result<_, _> = expression_trees
                    .iter()
                    .map(|e| WellFormed::check(e, symbols))
                    .collect();
                let es = r?;
                Ok(ExpressionTree::Sum(es))
            }
            ExpressionTree::Floor(a, b) => {
                let a = Box::new(WellFormed::check(a, symbols)?);
                let b = Box::new(WellFormed::check(b, symbols)?);
                let (b_min, b_max) = (b.min(symbols), b.max(symbols));
                // We conservatively reject anything that _contains zero in its range_,
                // even if the probability of a zero value is zero.
                if (b_min..=b_max).contains(&0) {
                    return Err(Error::DivideByZero(b.to_string()));
                }

                Ok(ExpressionTree::Floor(a, b))
            }
            ExpressionTree::Comparison { a, b, op } => {
                let a = Box::new(WellFormed::check(a, symbols)?);
                let b = Box::new(WellFormed::check(b, symbols)?);
                Ok(ExpressionTree::Comparison { a, b, op: *op })
            }

            ExpressionTree::Binding {
                symbol,
                value,
                tail,
            } => {
                if symbols.search(symbol).is_some() {
                    return Err(Error::SymbolRedefined(symbol.to_owned()));
                }
                let value = WellFormed::check(value, symbols)?;
                let next_avail = AvailableBinding::Chain {
                    defined: symbol,
                    definition: &value,
                    prev: symbols,
                };
                let tail = WellFormed::check(tail, &next_avail)?;
                Ok(ExpressionTree::Binding {
                    symbol: symbol.clone(),
                    value: Box::new(value),
                    tail: Box::new(tail),
                })
            }
        };
        tree.map(WellFormed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn undefined_reference() {
        let v: RawExpression = "[ABC: 1d20] BCD".parse().unwrap();
        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
        let e_target: Symbol = "BCD".parse().unwrap();
        match e {
            crate::Error::SymbolUndefined(sym) if sym == e_target => (),
            x => panic!("unexpected error: {x}"),
        }
    }

    #[test]
    fn redefined_reference() {
        let v: RawExpression = "[ABC: 1d20] [ABC:2d10] ABC + ABC".parse().unwrap();
        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
        let e_target = "ABC".parse().unwrap();
        assert!(matches!(e, crate::Error::SymbolRedefined(sym) if sym == e_target));
    }

    #[test]
    fn undefined_contextural() {
        let v: RawExpression = "2([ATK: 1d20] (ATK + 1 > 10) * 10) + ATK".parse().unwrap();
        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
        let e_target = "ATK".parse().unwrap();
        assert!(matches!(e, crate::Error::SymbolUndefined(sym) if sym == e_target));
    }

    #[test]
    fn keep_enough_high() {
        let v: RawExpression = "3d20kh4".parse().unwrap();
        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
        assert!(matches!(e, crate::Error::KeepTooFew(_, _)));
    }

    #[test]
    fn keep_enough_low() {
        let v: RawExpression = "3d20kl4".parse().unwrap();
        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
        assert!(matches!(e, crate::Error::KeepTooFew(_, _)));
    }

    #[test]
    fn no_zero_in_denominator_range() {
        let v: RawExpression = "10 / (1d20 - 10)".parse().unwrap();
        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
        assert!(matches!(e, crate::Error::DivideByZero(_)));
    }

    #[test]
    fn no_zero_faced_dice() {
        let v: RawExpression = "d0".parse().unwrap();
        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
        assert!(matches!(e, crate::Error::ZeroFacedDie()));
    }

    #[test]
    fn minimum() {
        for (i, (e, min)) in [
            ("20 / 2", 10),
            ("1d20 / 1d10", 0),
            ("-1d20", -20),
            ("1d20", 1),
            ("-1d20 / 1d20", -20),
            ("1d20 / -1d20", -20),
            ("[ATK: 1d20] ATK+3", 4),
            ("1d2 * 1d2", 1),
            ("1d2 < 2", 0),
            ("[ATK: 1d20] -ATK", -20),
            ("[ATK: -1d20] -ATK", 1),
        ]
        .into_iter()
        .enumerate()
        {
            let e: WellFormed = e.parse().unwrap();
            assert_eq!(e.minimum(), min, "case {i} for expression {e}");
        }
    }
    #[test]
    fn maximum() {
        for (i, (e, max)) in [
            ("20 / 2", 10),
            ("1d20 / 1d10", 20),
            ("-1d20", -1),
            ("1d20", 20),
            ("-1d20 / 1d20", 0),
            ("1d20 / -1d20", 0),
            ("[ATK: 1d20] ATK+3", 23),
            ("1d2 * 1d2", 4),
            ("1d2 > 1", 1),
            ("[ATK: 1d20] -ATK", -1),
            ("[ATK: -1d20] -ATK", 20),
        ]
        .into_iter()
        .enumerate()
        {
            let e: WellFormed = e.parse().unwrap();
            assert_eq!(e.maximum(), max, "case {i} for expression {e}");
        }
    }
}
