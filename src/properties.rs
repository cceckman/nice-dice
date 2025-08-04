//! Helpers for property-based testing.

use proptest::prelude::*;

use crate::symbolic::{ComparisonOp, ExpressionTree, ExpressionWrapper, Ranker, Symbol};

/// Generate a valid Symbol.
pub fn symbol() -> impl Strategy<Value = Symbol> {
    proptest::string::string_regex("[A-Z]+")
        .expect("valid regex")
        .prop_map(|s| s.parse().unwrap())
}

pub fn negated<W>(strat: &BoxedStrategy<W>) -> impl Strategy<Value = ExpressionTree<W>> + use<W>
where
    W: ExpressionWrapper + std::fmt::Debug,
{
    strat
        .clone()
        .prop_map(|v| ExpressionTree::Negated(Box::new(v)))
}

pub fn repeated<W>(strat: &BoxedStrategy<W>) -> impl Strategy<Value = ExpressionTree<W>> + use<W>
where
    W: ExpressionWrapper + std::fmt::Debug,
{
    (strat.clone(), strat.clone(), any::<Ranker>()).prop_map(|(count, value, ranker)| {
        ExpressionTree::Repeated {
            count: Box::new(count),
            value: Box::new(value),
            ranker,
        }
    })
}

pub fn product<W>(strat: &BoxedStrategy<W>) -> impl Strategy<Value = ExpressionTree<W>> + use<W>
where
    W: ExpressionWrapper + std::fmt::Debug,
{
    (strat.clone(), strat.clone())
        .prop_map(|(a, b)| ExpressionTree::Product(Box::new(a), Box::new(b)))
}

pub fn floor<W>(strat: &BoxedStrategy<W>) -> impl Strategy<Value = ExpressionTree<W>> + use<W>
where
    W: ExpressionWrapper + std::fmt::Debug,
{
    (strat.clone(), strat.clone())
        .prop_map(|(a, b)| ExpressionTree::Floor(Box::new(a), Box::new(b)))
}

pub fn sum<W>(strat: &BoxedStrategy<W>) -> impl Strategy<Value = ExpressionTree<W>> + use<W>
where
    W: ExpressionWrapper + std::fmt::Debug,
{
    prop::collection::vec(strat.clone(), 2..5).prop_map(ExpressionTree::Sum)
}

pub fn comparison<W>(strat: &BoxedStrategy<W>) -> impl Strategy<Value = ExpressionTree<W>> + use<W>
where
    W: ExpressionWrapper + std::fmt::Debug,
{
    (strat.clone(), strat.clone(), any::<ComparisonOp>()).prop_map(|(a, b, op)| {
        ExpressionTree::Comparison {
            a: Box::new(a),
            b: Box::new(b),
            op,
        }
    })
}
