//! Well-formedness checking (semantic analysis) of dice expressions.
//!
//! We need to make sure:
//! - All symbols are defined when used.
//! - Symbols do not conflict.
//! - Keep-highest / keep-lowest are always valid
//! - Division never divides by zero
//!
//!
//! TODO: Conditionals are nonlinear, so we can't generate min/max.
//! We have to just handle the whole path.

use std::{collections::HashSet, fmt::Display, str::FromStr};

use crate::{
    Error,
    parse::RawExpression,
    symbolic::{Constant, Die, ExpressionTree, ExpressionWrapper, Symbol},
};

impl TryFrom<RawExpression> for Closed {
    type Error = Error;

    fn try_from(value: RawExpression) -> Result<Self, Self::Error> {
        let tree = value.inner();
        closed_under(&AvailableBinding::Root, tree).map_err(Error::UnboundSymbols)
    }
}

/// An expression which is closed: no unbound symbols from its environment.
//
// Note that this really only applies at the top level: the sub-tree can't safely be extracted.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Closed(ExpressionTree<Closed>);

impl ExpressionWrapper for Closed {
    fn inner(&self) -> &ExpressionTree<Self> {
        &self.0
    }
}

impl Display for Closed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// Evaluate the expression under the provided bindings.
///
/// If the expression is closed under those bindings, return Ok();
/// otherwise, return the unbound symbol(s).
fn closed_under(
    bindings: &AvailableBinding<Closed>,
    tree: &ExpressionTree<RawExpression>,
) -> Result<Closed, HashSet<Symbol>> {
    match tree {
        ExpressionTree::Modifier(a) => Ok(Closed(ExpressionTree::Modifier(*a))),
        ExpressionTree::Die(a) => Ok(Closed(ExpressionTree::Die(*a))),
        ExpressionTree::Symbol(symbol) => {
            if bindings.search(symbol).is_some() {
                Ok(Closed(ExpressionTree::Symbol(symbol.to_owned())))
            } else {
                Err([symbol.clone()].into_iter().collect::<HashSet<_>>())
            }
        }
        ExpressionTree::Negated(n) => Ok(Closed(ExpressionTree::Negated(Box::new(closed_under(
            bindings,
            n.inner(),
        )?)))),
        ExpressionTree::Repeated {
            count,
            value,
            ranker,
        } => {
            let count = closed_under(bindings, count.inner())?;
            let value = closed_under(bindings, value.inner())?;
            let count = Box::new(count);
            let value = Box::new(value);
            Ok(Closed(ExpressionTree::Repeated {
                count,
                value,
                ranker: *ranker,
            }))
        }
        ExpressionTree::Product(a, b) => {
            let a = closed_under(bindings, a.inner())?;
            let b = closed_under(bindings, b.inner())?;
            Ok(Closed(ExpressionTree::Product(Box::new(a), Box::new(b))))
        }
        ExpressionTree::Sum(items) => {
            let items: Result<_, _> = items
                .iter()
                .map(|item| closed_under(bindings, item.inner()))
                .collect();
            let items = items?;
            Ok(Closed(ExpressionTree::Sum(items)))
        }
        ExpressionTree::Floor(a, b) => {
            let a = closed_under(bindings, a.inner())?;
            let b = closed_under(bindings, b.inner())?;
            Ok(Closed(ExpressionTree::Floor(Box::new(a), Box::new(b))))
        }
        ExpressionTree::Comparison { a, b, op } => {
            let a = closed_under(bindings, a.inner())?;
            let b = closed_under(bindings, b.inner())?;
            Ok(Closed(ExpressionTree::Comparison {
                a: Box::new(a),
                b: Box::new(b),
                op: *op,
            }))
        }

        ExpressionTree::Binding {
            symbol,
            value,
            tail,
        } => {
            let value = closed_under(bindings, value.inner())?;
            let tail = closed_under(
                &AvailableBinding::Chain {
                    defined: symbol,
                    definition: &value,
                    prev: bindings,
                },
                tail.inner(),
            )?;
            Ok(Closed(ExpressionTree::Binding {
                symbol: symbol.clone(),
                value: Box::new(value),
                tail: Box::new(tail),
            }))
        }
    }
}

/// Linked list (on the stack) of current symbol bindings.
#[derive(Copy, Clone)]
enum AvailableBinding<'a, T: ExpressionWrapper> {
    Root,
    Chain {
        defined: &'a Symbol,
        definition: &'a T,
        prev: &'a AvailableBinding<'a, T>,
    },
}

impl<T: ExpressionWrapper> AvailableBinding<'_, T> {
    /// Search the stack of bindings for the provided symbol.
    fn search(&self, needle: &Symbol) -> Option<&T> {
        let mut current: &AvailableBinding<T> = self;
        while let AvailableBinding::Chain {
            defined,
            prev,
            definition,
        } = current
        {
            if *defined == needle {
                return Some(definition);
            } else {
                current = *prev;
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use proptest::strategy::Union;

    use super::*;
    use crate::parse::RawExpression;
    use crate::properties;

    // TODO: These don't work correctly;
    // And they don't shrink well, which hurts too.
    //
    // I think the "recurse in both directions" is a problem-
    // that one of our "recursive strategies" is generating something of arbitrary depth.
    // I think that's a problem for the srhinkage.
    //
    // Not sure what the right way to put these together is.
    // Maybe:
    //

    /// Inner generator: produces a strategy for expressions closed under the given set of symbols.
    /// Preserves the set of available symbols.
    /// Does not introduce any bindings.
    fn expression_closed_under(
        symbols: HashSet<Symbol>,
    ) -> impl Strategy<Value = (RawExpression, HashSet<Symbol>)> {
        let symbols_final = symbols.clone();
        let leaf = Union::new([
            any::<Die>().prop_map(ExpressionTree::Die).boxed(),
            any::<Constant>().prop_map(ExpressionTree::Modifier).boxed(),
        ]);

        let leaf = if symbols.is_empty() {
            leaf
        } else {
            let symbol = (0..symbols.len())
                .prop_map(move |v| {
                    let s = symbols.iter().nth(v).unwrap();
                    ExpressionTree::Symbol(s.clone())
                })
                .boxed();

            leaf.or(symbol)
        };

        let leaf = leaf.prop_map(RawExpression::from);
        let closure = leaf.prop_recursive(2, 2, 2, |strat| {
            prop_oneof![
                properties::negated(&strat),
                properties::repeated(&strat),
                properties::product(&strat),
                properties::floor(&strat),
                properties::sum(&strat),
                properties::comparison(&strat),
            ]
            .prop_map(RawExpression::from)
        });
        closure.prop_map(move |v| (v, symbols_final.clone()))
    }

    proptest! {
        #[test]
        fn identify_open_symbols(
            (symbols, (exp, _)) in
            proptest::collection::hash_set(properties::symbol(), 1..4)
            .prop_flat_map(|symbols| (Just(symbols.clone()), expression_closed_under(symbols)))
        ) {
            // TODO: This assumes the symbols are used... which they need not be.
            let result : Result<Closed, _> = exp.clone().try_into();
            let Err(Error::UnboundSymbols(got)) = result else {
                return Err(TestCaseError::fail(format!("expression: {exp}")));
            };
            assert_eq!(got, symbols);
        }
    }

    /// Generate an Expression with valid bindings.
    fn closed_expression() -> impl Strategy<Value = RawExpression> {
        let leaf = expression_closed_under(HashSet::new());
        let syms = leaf.prop_recursive(2, 2, 2, |strat| {
            (properties::symbol(), strat.clone()).prop_flat_map(
                |(symbol, (definition, mut symbols))| {
                    // In the symbol-recursive case, we:
                    // - select a symbol
                    // - generate a binding from our _existing_ strategy... which takes into account
                    //   symbols already defined
                    // - create a _new_ strategy including our symbol the others, to generate the tail
                    //   with
                    symbols.insert(symbol.clone());
                    expression_closed_under(symbols).prop_map(move |(tail, new_symbols)| {
                        (
                            RawExpression::from(ExpressionTree::Binding {
                                symbol: symbol.clone(),
                                value: Box::new(definition.clone()),
                                tail: Box::new(tail),
                            }),
                            new_symbols,
                        )
                    })
                },
            )
        });
        syms.prop_map(|(tree, _syms)| tree)
    }

    proptest! {
        #[test]
        fn generate_valid_bindings(exp in closed_expression()) {
            let exp = exp.simplify();
            let s = exp.to_string();
            let _ : Closed = exp.try_into().map_err(|e| {
                TestCaseError::fail(format!("expression: {s}\n{e}"))
            })?;
        }
    }
}

//#[cfg(test)]
//mod tests {
//    use super::*;
//
//    #[test]
//    fn undefined_reference() {
//        let v: RawExpression = "[ABC: 1d20] BCD".parse().unwrap();
//        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
//        let e_target: Symbol = "BCD".parse().unwrap();
//        match e {
//            crate::Error::SymbolUndefined(sym) if sym == e_target => (),
//            x => panic!("unexpected error: {x}"),
//        }
//    }
//
//    #[test]
//    fn redefined_reference() {
//        let v: RawExpression = "[ABC: 1d20] [ABC:2d10] ABC + ABC".parse().unwrap();
//        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
//        let e_target = "ABC".parse().unwrap();
//        assert!(matches!(e, crate::Error::SymbolRedefined(sym) if sym == e_target));
//    }
//
//    #[test]
//    fn undefined_contextural() {
//        let v: RawExpression = "2([ATK: 1d20] (ATK + 1 > 10) * 10) + ATK".parse().unwrap();
//        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
//        let e_target = "ATK".parse().unwrap();
//        assert!(matches!(e, crate::Error::SymbolUndefined(sym) if sym == e_target));
//    }
//
//    #[test]
//    fn keep_enough_high() {
//        let v: RawExpression = "3d20kh4".parse().unwrap();
//        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
//        assert!(matches!(e, crate::Error::KeepTooFew(_, _)));
//    }
//
//    #[test]
//    fn keep_enough_low() {
//        let v: RawExpression = "3d20kl4".parse().unwrap();
//        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
//        assert!(matches!(e, crate::Error::KeepTooFew(_, _)));
//    }
//
//    #[test]
//    fn no_zero_in_denominator_range() {
//        let v: RawExpression = "10 / (1d20 - 10)".parse().unwrap();
//        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
//        assert!(matches!(e, crate::Error::DivideByZero(_)));
//    }
//
//    #[test]
//    fn no_zero_faced_dice() {
//        let v: RawExpression = "d0".parse().unwrap();
//        let e = std::convert::TryInto::<WellFormed>::try_into(v).unwrap_err();
//        assert!(matches!(e, crate::Error::ZeroFacedDie()));
//    }
//
//    #[test]
//    fn minimum() {
//        for (i, (e, min)) in [
//            ("20 / 2", 10),
//            ("1d20 / 1d10", 0),
//            ("-1d20", -20),
//            ("1d20", 1),
//            ("-1d20 / 1d20", -20),
//            ("1d20 / -1d20", -20),
//            ("[ATK: 1d20] ATK+3", 4),
//            ("1d2 * 1d2", 1),
//            ("1d2 < 2", 0),
//            ("[ATK: 1d20] -ATK", -20),
//            ("[ATK: -1d20] -ATK", 1),
//            ("2d10", 2),
//        ]
//        .into_iter()
//        .enumerate()
//        {
//            let e: WellFormed = e.parse().unwrap();
//            assert_eq!(e.minimum(), min, "case {i} for expression {e}");
//        }
//    }
//    #[test]
//    fn maximum() {
//        for (i, (e, max)) in [
//            ("20 / 2", 10),
//            ("1d20 / 1d10", 20),
//            ("-1d20", -1),
//            ("1d20", 20),
//            ("-1d20 / 1d20", 0),
//            ("1d20 / -1d20", 0),
//            ("[ATK: 1d20] ATK+3", 23),
//            ("1d2 * 1d2", 4),
//            ("1d2 > 1", 1),
//            ("[ATK: 1d20] -ATK", -1),
//            ("[ATK: -1d20] -ATK", 20),
//            ("2d10", 20),
//        ]
//        .into_iter()
//        .enumerate()
//        {
//            let e: WellFormed = e.parse().unwrap();
//            assert_eq!(e.maximum(), max, "case {i} for expression {e}");
//        }
//    }
//
//    #[test]
//    #[ignore = "TODO: Incorrect; breaks linearity assumption"]
//    fn attack_rolls() {
//        // Complicated ones: Eldritch Blast, with Agonizing Blast, including critical effects.
//        for (i, (e, max)) in [
//            ("[AC: 16] [CHA: +5] [ATK: 1d20] (ATK = 20) * (2d10 + CHA) + (ATK < 20) * (ATK > 1) * (ATK + CHA >= AC) * (1d10 + CHA)", 25),
//            ("2([AC: 16] [ATK: 1d20] [CHA: +5] (ATK = 20) * (2d10 + CHA) + (ATK < 20) * (ATK > 1) * (ATK + CHA >= AC) * (1d10 + CHA))", 50),
//            ("[AC: 16] [CHA: +5] 2([ATK: 1d20] (ATK = 20) * (2d10 + CHA) + (ATK < 20) * (ATK > 1) * (ATK + CHA >= AC) * (1d10 + CHA))", 50),
//        ].into_iter().enumerate() {
//            let e : WellFormed = e.parse().unwrap();
//            assert_eq!(e.minimum(), 0); // critical miss
//            assert_eq!(e.maximum(), max); // critical miss
//        }
//    }
//}
