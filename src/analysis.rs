//! Well-formedness checking (semantic analysis) of dice expressions.
//!
//! We need to make sure:
//! - All symbols are defined when used.
//! - Symbols do not conflict.
//! - Keep-highest / keep-lowest are always valid (TODO: but do we?)
//!

use crate::{
    Error,
    symbolic::{ExpressionTree, Symbol},
};

/// An dice expression that is well-formed per semantic analysis.
///
/// - All symbols are declared before use, in the context of their use.
/// -
#[derive(Debug)]
pub struct WellFormed(ExpressionTree);

type RawExpression = ExpressionTree;

impl TryFrom<RawExpression> for WellFormed {
    type Error = Error;

    fn try_from(value: RawExpression) -> Result<Self, Self::Error> {
        WellFormed::check(&value, &AvailableBinding::Root)?;
        Ok(WellFormed(value))
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
    /// Recursively check that this expression is well-formed, given the provided stack of
    /// bindings.
    fn check<'a>(target: &'a RawExpression, symbols: &AvailableBinding) -> Result<(), Error> {
        match target {
            ExpressionTree::Modifier(_) => Ok(()),
            ExpressionTree::Die(_) => Ok(()),
            ExpressionTree::Symbol(symbol) => {
                if symbols.search(symbol).is_some() {
                    Ok(())
                } else {
                    Err(Error::SymbolUndefined(symbol.to_owned()))
                }
            }
            ExpressionTree::Negated(expression_tree) => WellFormed::check(expression_tree, symbols),
            ExpressionTree::Repeated {
                count,
                value,
                ranker,
            } => {
                // Individually well-formed:
                WellFormed::check(count, symbols)
                    .and_then(|_| WellFormed::check(value, symbols))?;

                // And also, we are guaranteed to have at least the given number.
                if count.min() < ranker.count() {
                    return Err(Error::KeepTooFew(ranker.count(), count.to_string()));
                }
                Ok(())
            }
            ExpressionTree::Product(a, b) => {
                WellFormed::check(a, symbols).and_then(|_| WellFormed::check(b, symbols))
            }
            ExpressionTree::Sum(expression_trees) => {
                for es in expression_trees.iter() {
                    WellFormed::check(es, symbols)?;
                }
                Ok(())
            }
            ExpressionTree::Floor(a, b) => {
                WellFormed::check(a, symbols).and_then(|_| WellFormed::check(b, symbols))
            }
            ExpressionTree::Comparison { a, b, op: _ } => {
                WellFormed::check(a, symbols).and_then(|_| WellFormed::check(b, symbols))
            }

            ExpressionTree::Binding {
                symbol,
                value,
                tail,
            } => {
                if symbols.search(symbol).is_some() {
                    return Err(Error::SymbolRedefined(symbol.to_owned()));
                }
                WellFormed::check(value, symbols)?;
                let next_avail = AvailableBinding::Chain {
                    defined: symbol,
                    definition: WellFormed
                    prev: symbols,

                };
                WellFormed::check(tail, &next_avail)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn undefined_reference() {
        let v: RawExpression = "[ABC: 1d20] BCD".parse().unwrap();
        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
        let e_target = "BCD".parse().unwrap();
        assert!(matches!(e, crate::Error::SymbolUndefined(sym) if sym == e_target));
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
        assert!(matches!(e, crate::Error::KeepTooFew(_)));
    }

    #[test]
    fn keep_enough_low() {
        let v: RawExpression = "3d20kl4".parse().unwrap();
        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
        assert!(matches!(e, crate::Error::KeepTooFew(_)));
    }
}
