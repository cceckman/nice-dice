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

use std::{collections::HashSet, fmt::Display};

use crate::{
    Error,
    parse::RawExpression,
    symbolic::{ExpressionTree, ExpressionWrapper, Symbol},
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

type ClosureResult = Result<Closed, HashSet<Symbol>>;

fn combine_close_results(
    a: ClosureResult,
    b: ClosureResult,
) -> Result<(Closed, Closed), HashSet<Symbol>> {
    match (a, b) {
        (Ok(a), Ok(b)) => Ok((a, b)),
        (Err(a), Err(b)) => Err(a.into_iter().chain(b).collect()),
        (Err(a), _) => Err(a),
        (_, Err(b)) => Err(b),
    }
}

/// Evaluate the expression under the provided bindings.
///
/// If the expression is closed under those bindings, return Ok();
/// otherwise, return the unbound symbol(s).
fn closed_under(
    bindings: &AvailableBinding<Closed>,
    tree: &ExpressionTree<RawExpression>,
) -> ClosureResult {
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
            let (count, value) = combine_close_results(
                closed_under(bindings, count.inner()),
                closed_under(bindings, value.inner()),
            )?;
            let count = Box::new(count);
            let value = Box::new(value);
            Ok(Closed(ExpressionTree::Repeated {
                count,
                value,
                ranker: *ranker,
            }))
        }
        ExpressionTree::Product(a, b) => {
            let (a, b) = combine_close_results(
                closed_under(bindings, a.inner()),
                closed_under(bindings, b.inner()),
            )?;
            Ok(Closed(ExpressionTree::Product(Box::new(a), Box::new(b))))
        }
        ExpressionTree::Sum(items) => {
            let mut unbound: HashSet<Symbol> = Default::default();
            let items: Vec<Closed> = items
                .iter()
                .filter_map(|item| match closed_under(bindings, item.inner()) {
                    Ok(v) => Some(v),
                    Err(e) => {
                        for e in e {
                            unbound.insert(e);
                        }
                        None
                    }
                })
                .collect();
            if unbound.is_empty() {
                Ok(Closed(ExpressionTree::Sum(items)))
            } else {
                Err(unbound)
            }
        }
        ExpressionTree::Floor(a, b) => {
            let (a, b) = combine_close_results(
                closed_under(bindings, a.inner()),
                closed_under(bindings, b.inner()),
            )?;
            Ok(Closed(ExpressionTree::Floor(Box::new(a), Box::new(b))))
        }
        ExpressionTree::Comparison { a, b, op } => {
            let (a, b) = combine_close_results(
                closed_under(bindings, a.inner()),
                closed_under(bindings, b.inner()),
            )?;
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
    use crate::symbolic::{Constant, Die};

    #[test]
    fn open_symbols() {
        const CASES: &[(&str, &[&str])] = &[
            ("ATK", &["ATK"]),
            ("2(ATK+CHA)", &["ATK", "CHA"]),
            ("[AC: 10] [ATK: 1d20] (ATK + CHA) > AC", &["CHA"]),
        ];
        for (expr, symbols) in CASES {
            let raw: RawExpression = expr.parse().unwrap();
            let symbols: HashSet<Symbol> = symbols.iter().map(|v| v.parse().unwrap()).collect();
            let unclosed: Result<Closed, _> = raw.try_into();
            let Err(Error::UnboundSymbols(unbound)) = unclosed else {
                panic!("got closed expression")
            };
            assert_eq!(symbols, unbound, "case: {expr}");
        }
    }

    #[test]
    fn closed_symbols() {
        const CASES: &[&str] = &["[AC: 10] 2([ATK: 1d20] (ATK + 3) > AC)"];
        for expr in CASES {
            let raw: RawExpression = expr.parse().unwrap();
            let closed: Closed = raw.clone().try_into().unwrap();
            assert_eq!(closed.to_string(), raw.to_string());
        }
    }

    /// Search for an expression that matches the predicate
    fn search_for<'a, T, F>(
        tree: &'a ExpressionTree<T>,
        predicate: &mut F,
    ) -> Option<&'a ExpressionTree<T>>
    where
        F: FnMut(&ExpressionTree<T>) -> bool,
        T: ExpressionWrapper,
    {
        if predicate(tree) {
            return Some(tree);
        }
        match tree {
            ExpressionTree::Negated(e) => search_for(e.inner(), predicate),
            ExpressionTree::Repeated {
                count,
                value,
                ranker: _,
            } => search_for(count.inner(), predicate).or(search_for(value.inner(), predicate)),
            ExpressionTree::Product(a, b) => {
                search_for(a.inner(), predicate).or(search_for(b.inner(), predicate))
            }
            ExpressionTree::Floor(a, b) => {
                search_for(a.inner(), predicate).or(search_for(b.inner(), predicate))
            }
            ExpressionTree::Comparison { a, b, op: _ } => {
                search_for(a.inner(), predicate).or(search_for(b.inner(), predicate))
            }
            ExpressionTree::Sum(items) => {
                for item in items {
                    if let Some(v) = search_for(item.inner(), predicate) {
                        return Some(v);
                    }
                }
                None
            }
            ExpressionTree::Binding {
                symbol,
                value,
                tail,
            } => search_for(value.inner(), predicate).or(search_for(tail.inner(), predicate)),

            _ => None,
        }
    }

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

        let static_leaf = Union::new([
            any::<Die>().prop_map(ExpressionTree::Die).boxed(),
            any::<Constant>().prop_map(ExpressionTree::Modifier).boxed(),
        ]);

        // If any symbols are available, only use those symbols.
        // This guarantees that symbols show up when in use.
        let leaf = if symbols.is_empty() {
            static_leaf.boxed()
        } else {
            (0..symbols.len())
                .prop_map(move |v| {
                    let s = symbols.iter().nth(v).unwrap();
                    ExpressionTree::Symbol(s.clone())
                })
                .boxed()
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
            (_symbols, (exp, _)) in
            proptest::collection::hash_set(properties::symbol(), 1..4)
            .prop_flat_map(|symbols| (Just(symbols.clone()), expression_closed_under(symbols)))
        ) {
            let result : Result<Closed, _> = exp.clone().try_into();

            if let Err(Error::UnboundSymbols(got)) = result {
                for symbol in got {
                    // The symbol is used:
                    assert!(search_for(exp.inner(), &mut |s| matches!(s, ExpressionTree::Symbol(sym) if sym == &symbol)).is_some());
                }
            }
        }
        // The generator doesn't introduce any bindings, so we don't need to test the binding
        // hierarchy here.
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

    /// Matches a tree where the symbol is unbound.
    fn unbound_tree<'a, W>(
        symbol: &Symbol,
        tree: &'a ExpressionTree<W>,
    ) -> Option<&'a ExpressionTree<W>>
    where
        W: ExpressionWrapper,
    {
        match tree {
            ExpressionTree::Binding {
                symbol: sym,
                value,
                tail,
            } => {
                // Symbol is unbound in the "value" statement
                let value = unbound_tree(symbol, value.inner());
                if sym == symbol {
                    // Symbol is bound in the tail, we don't need to inspect it.
                    value
                } else {
                    // Symbol is also unbound in the tail, look there.
                    value.or_else(|| unbound_tree(symbol, tail.inner()))
                }
            }
            ExpressionTree::Modifier(_) => None,
            ExpressionTree::Die(_) => None,
            ExpressionTree::Symbol(sym) if sym == symbol => Some(tree),
            ExpressionTree::Symbol(_) => None,
            ExpressionTree::Negated(e) => unbound_tree(symbol, e.inner()),
            ExpressionTree::Repeated {
                count,
                value,
                ranker: _,
            } => {
                unbound_tree(symbol, count.inner()).or_else(|| unbound_tree(symbol, value.inner()))
            }
            ExpressionTree::Product(a, b) => {
                unbound_tree(symbol, a.inner()).or_else(|| unbound_tree(symbol, b.inner()))
            }
            ExpressionTree::Floor(a, b) => {
                unbound_tree(symbol, a.inner()).or_else(|| unbound_tree(symbol, b.inner()))
            }
            ExpressionTree::Comparison { a, b, op: _ } => {
                unbound_tree(symbol, a.inner()).or_else(|| unbound_tree(symbol, b.inner()))
            }
            ExpressionTree::Sum(items) => items
                .iter()
                .filter_map(|v| unbound_tree(symbol, v.inner()))
                .next(),
        }
    }

    proptest! {
        // TODO: This tests that all _detected_ unbound variables are in fact unbound.
        // It doesn't check that all unbound variables are detected.
        #[test]
        fn generate_valid_bindings(exp in closed_expression()) {
            let exp = exp.simplify();
            let result : Result<Closed, _> = exp.clone().try_into();
            if let Err(Error::UnboundSymbols(got)) = result {
                for symbol in got {
                    // The symbol is used:
                    assert!(search_for(exp.inner(), &mut |s| matches!(s, ExpressionTree::Symbol(sym) if sym == &symbol)).is_some());

                    // And there is some sub tree where:
                    // - There is no binding for the symbol, and
                    // - The symbol is used
                    assert!(unbound_tree(&symbol, exp.inner()).is_some());
                }
            }


        }
    }
}
