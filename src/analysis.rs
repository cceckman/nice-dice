//! Well-formedness checking (semantic analysis) of dice expressions.
//!
//! We need to make sure:
//! - All symbols are defined when used.
//! - Symbols do not conflict.
//! - Keep-highest / keep-lowest are always valid (TODO: but do we?)
//!

use crate::{
    Error,
    parse::RawExpression,
    symbolic::{ExpressionTree, ExpressionWrapper, Symbol},
};

/// An dice expression that is well-formed per semantic analysis.
///
/// - All symbols are declared before use, in the context of their use.
/// -
#[derive(Debug)]
pub struct WellFormed(ExpressionTree<WellFormed>);

impl TryFrom<RawExpression> for WellFormed {
    type Error = Error;

    fn try_from(value: RawExpression) -> Result<Self, Self::Error> {
        WellFormed::check(&value, &AvailableBinding::Root)
    }
}

impl From<ExpressionTree<WellFormed>> for WellFormed {
    fn from(value: ExpressionTree<WellFormed>) -> Self {
        WellFormed(value)
    }
}

impl ExpressionWrapper for WellFormed {
    fn inner(&self) -> &ExpressionTree<Self> {
        &self.0
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
    fn check(target: &RawExpression, symbols: &AvailableBinding) -> Result<WellFormed, Error> {
        let tree: Result<ExpressionTree<WellFormed>, _> = match target.inner() {
            ExpressionTree::Modifier(m) => Ok(ExpressionTree::Modifier(*m)),
            ExpressionTree::Die(d) => Ok(ExpressionTree::Die(*d)),
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

                Ok(ExpressionTree::Repeated {
                    count,
                    value,
                    ranker: *ranker,
                })
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
}
