//! Probability computation via discrete (integral) math and combinatorics.

use crate::{
    Error,
    analysis::Closed,
    symbolic::{ComparisonOp, Constant, Die, ExpressionTree, ExpressionWrapper, Ranker, Symbol},
};
use std::{collections::HashMap, ops::Neg};

use itertools::Itertools;
use num::{ToPrimitive, rational::Ratio};

/// A computed distribution for a bounded dice expression.
/// ("bounded": does not support exploding dice.)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Distribution {
    /// We track probabilities of each value using integers;
    /// all of these have an implied denominator of occurrence_by_value.sum().
    occurrence_by_value: Vec<usize>,
    /// Index i in occurrence_by_value represents the number of occurrences of (i+offset).
    offset: isize,
}

/// An evaluator: evaluates distributions for a closed expression.
///
/// Evaluators provide memoization for sub-expressions.
/// It may be useful to re-use an Evaluator when experimenting with new expressions,
/// trading (some) memory for (some) processing.
///
// TODO: Benchmark with and without memoization.
#[derive(Default)]
struct Evaluator {
    /// Memoization table.
    memo: HashMap<Closed, Distribution>,
    use_memo: bool,
}

impl Evaluator {
    fn eval(&mut self, tree: &Closed) -> Result<Distribution, Error> {
        if self.use_memo {
            if let Some(dist) = self.memo.get(tree) {
                return Ok(dist.clone());
            }
        }
        // We begin with native-stack recursion.

        // Need to evaluate.
        let memo = match tree.inner() {
            ExpressionTree::Modifier(Constant(constant)) => Distribution::constant(*constant),
            ExpressionTree::Die(Die(die)) => Distribution::die(*die),
            ExpressionTree::Symbol(symbol) => {
                panic!("unbound symbol {symbol} in closed expression")
                // return Err(Error::UnboundSymbols([symbol].into()))
            }
            ExpressionTree::Negated(e) => {
                let dist = self.eval(e.as_ref())?;
                -dist
            }
            ExpressionTree::Repeated {
                count,
                value,
                ranker,
            } => self.repeat(tree, count, value, ranker)?,
            ExpressionTree::Product(a, b) => self.product(a, b)?,
            ExpressionTree::Floor(a, b) => self.floor(tree, a, b)?,
            ExpressionTree::Sum(items) => {
                let distrs: Result<Vec<_>, _> = items.iter().map(|e| self.eval(e)).collect();
                let distrs = distrs?;
                distrs.into_iter().sum()
            }
            ExpressionTree::Comparison { a, b, op } => self.comparison(a, b, *op)?,
            ExpressionTree::Binding {
                symbol,
                value,
                tail,
            } => self.binding(symbol, value, tail)?,
        };
        if self.use_memo {
            self.memo.insert(tree.clone(), memo.clone());
        }
        Ok(memo)
    }

    fn product(&mut self, a: &Closed, b: &Closed) -> Result<Distribution, Error> {
        let a = self.eval(a)?;
        let b = self.eval(b)?;

        let mut d = Distribution::empty();

        for ((v1, f1), (v2, f2)) in a.occurrences().cartesian_product(b.occurrences()) {
            d.add_occurrences(v1 * v2, f1 * f2);
        }
        Ok(d)
    }

    fn floor(&mut self, e: &Closed, a: &Closed, b: &Closed) -> Result<Distribution, Error> {
        let a = self.eval(a)?;
        let b = self.eval(b)?;

        if *b.probability(0).numer() != 0 {
            return Err(Error::DivideByZero(e.to_string()));
        }

        let mut d = Distribution::empty();
        for ((v1, f1), (v2, f2)) in a.occurrences().cartesian_product(b.occurrences()) {
            d.add_occurrences(v1 / v2, f1 * f2);
        }
        Ok(d)
    }

    fn repeat(
        &mut self,
        expression: &Closed,
        count: &Closed,
        value: &Closed,
        ranker: &Ranker,
    ) -> Result<Distribution, Error> {
        let count_dist = self.eval(count)?;
        let value_dist = self.eval(value)?;

        let mut result = Distribution::empty();
        if count_dist.min() < 0 {
            return Err(Error::NegativeCount(expression.to_string()));
        }
        if (count_dist.min() as usize) < ranker.min_count() {
            return Err(Error::KeepTooFew(
                ranker.min_count(),
                expression.to_string(),
            ));
        }

        // We have to have the same type signature for each of these,
        // and we want to truncate in the other cases.
        #[allow(clippy::ptr_arg)]
        fn keep_all(v: &mut [isize], _n: usize) -> &[isize] {
            v
        }
        fn keep_highest(v: &mut [isize], n: usize) -> &[isize] {
            v.sort_by(|v1, v2| v2.cmp(v1));
            &v[..n]
        }
        fn keep_lowest(v: &mut [isize], n: usize) -> &[isize] {
            v.sort();
            &v[..n]
        }
        let filter = match ranker {
            Ranker::All => keep_all,
            Ranker::Highest(_) => keep_highest,
            Ranker::Lowest(_) => keep_lowest,
        };

        for (count, count_frequency) in count_dist.occurrences() {
            let keep_count = ranker.keep(count) as usize;
            // Assuming this count happens this often...
            let dice = std::iter::repeat(&value_dist)
                .map(|d| d.occurrences())
                .take(count as usize);
            for value_set in dice.multi_cartesian_product() {
                let (mut values, frequencies): (Vec<isize>, Vec<usize>) =
                    value_set.into_iter().unzip();
                // We have to compute the overall frquency including the dice we dropped;
                // in other universes (other combinations), we'd keep them.
                let occurrences = frequencies.into_iter().product::<usize>() * count_frequency;
                let value = filter(&mut values, keep_count).iter().sum();
                result.add_occurrences(value, occurrences);
            }
        }
        Ok(result)
    }

    fn comparison(
        &mut self,
        a: &Closed,
        b: &Closed,
        op: ComparisonOp,
    ) -> Result<Distribution, Error> {
        let a = self.eval(a)?;
        let b = self.eval(b)?;

        let mut dist = Distribution::empty();

        for ((v1, o1), (v2, o2)) in a.occurrences().cartesian_product(b.occurrences()) {
            let occurrences = o1 * o2;
            let value = op.compare(v1, v2) as isize;
            dist.add_occurrences(value, occurrences);
        }
        Ok(dist)
    }

    fn binding(
        &mut self,
        symbol: &Symbol,
        value: &Closed,
        tail: &Closed,
    ) -> Result<Distribution, Error> {
        let value = self.eval(value)?;
        let mut acc = Distribution::empty();
        for (value, occ) in value.occurrences() {
            let tree: Closed = tail.substitute(symbol, value);
            let table = self.eval(&tree)?;
            for (v2, o2) in table.occurrences() {
                acc.add_occurrences(v2, occ * o2);
            }
        }
        Ok(acc)
    }
}

impl Distribution {
    /// Generate a uniform distribution on the closed interval `[1, size]`;
    /// i.e. the distribution for rolling a die with the given number of faces.
    fn die(size: usize) -> Distribution {
        let mut v = Vec::new();
        v.resize(size, 1);
        Distribution {
            occurrence_by_value: v,
            offset: 1,
        }
    }

    /// Generate a "modifier" distribution, which has probability 1 of producing the given value.
    fn constant(value: usize) -> Distribution {
        Distribution {
            occurrence_by_value: vec![1],
            offset: value as isize,
        }
    }

    /// Give the probability of this value occurring in this distribution.
    pub fn probability(&self, value: isize) -> Ratio<usize> {
        let index = value - self.offset;
        if (0..(self.occurrence_by_value.len() as isize)).contains(&index) {
            Ratio::new(self.occurrence_by_value[index as usize], self.total())
        } else {
            Ratio::new(0, 1)
        }
    }

    pub fn probability_f64(&self, value: isize) -> f64 {
        Ratio::to_f64(&self.probability(value)).expect("should convert probability to f64")
    }

    /// Report the total number of occurrences in this expression, i.e. the number of possible
    /// rolls (rather than the number of distinct values).
    pub fn total(&self) -> usize {
        let v = self.occurrence_by_value.iter().sum();
        debug_assert_ne!(v, 0);
        v
    }

    /// Iterator over (value, occurrences) tuples in this distribution.
    /// Reports values with nonzero occurrence in ascending order of value.
    pub fn occurrences(&self) -> Occurrences {
        Occurrences {
            distribution: self,
            current: self.offset,
        }
    }

    /// The minimum value with nonzero occurrence in this distribution.
    pub fn min(&self) -> isize {
        self.offset
    }

    /// The minimum value with nonzero occurrence in this distribution (note: inclusive)
    pub fn max(&self) -> isize {
        self.offset + (self.occurrence_by_value.len() as isize) - 1
    }

    /// The average value (expected value) from this distribution.
    pub fn mean(&self) -> f64 {
        // This might be a hefty sum, so keep each term in the f64 range, and sum f64s.
        (self.min()..=self.max())
            .map(|v| (v as f64) * self.probability_f64(v))
            .sum()
    }

    /// Clean up the distribution by removing extraneous zero-valued entries.
    fn clean(&mut self) {
        let leading_zeros = self
            .occurrence_by_value
            .iter()
            .take_while(|&&f| f == 0)
            .count();
        if leading_zeros > 0 {
            self.occurrence_by_value = self.occurrence_by_value[leading_zeros..].into();
            self.offset += leading_zeros as isize;
        }
        let trailing_zeros = self
            .occurrence_by_value
            .iter()
            .rev()
            .take_while(|&&f| f == 0)
            .count();
        self.occurrence_by_value
            .truncate(self.occurrence_by_value.len() - trailing_zeros);
    }

    /// Add the given occurrences to the values table.
    fn add_occurrences(&mut self, value: isize, occurrences: usize) {
        if value < self.offset {
            let diff = (self.offset - value) as usize;
            let new_len = self.occurrence_by_value.len() + diff;
            self.occurrence_by_value.resize(new_len, 0);
            // Swap "upwards", starting from the newly long end
            for i in (diff..self.occurrence_by_value.len()).rev() {
                self.occurrence_by_value.swap(i, i - diff);
            }
            self.offset = value;
        }
        let index = (value - self.offset) as usize;
        if index >= self.occurrence_by_value.len() {
            self.occurrence_by_value.resize(index + 1, 0);
        }
        self.occurrence_by_value[index] += occurrences;
    }

    fn empty() -> Self {
        Self {
            occurrence_by_value: vec![],
            offset: 0,
        }
    }
}

/// An iterator over the occurrences in a distribution.
///
/// Implemented explicitly for its Clone implementation.
#[derive(Debug, Clone)]
pub struct Occurrences<'a> {
    distribution: &'a Distribution,
    current: isize,
}

impl Iterator for Occurrences<'_> {
    type Item = (isize, usize);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let value = self.current;
            let index = (value - self.distribution.offset) as usize;
            if index < self.distribution.occurrence_by_value.len() {
                self.current += 1;
                let occ = self.distribution.occurrence_by_value[index];
                if occ == 0 {
                    continue;
                } else {
                    break Some((value, occ));
                }
            } else {
                break None;
            }
        }
    }
}

impl std::ops::Add<&Distribution> for &Distribution {
    type Output = Distribution;

    fn add(self, rhs: &Distribution) -> Self::Output {
        let a = self;
        let b = rhs;

        let mut result = Distribution::empty();

        for ((v1, o1), (v2, o2)) in a.occurrences().cartesian_product(b.occurrences()) {
            let val = v1 + v2;
            // aocc and bocc each represent the numerator of a fraction, aocc/atotal and
            // bocc/btotal. That fraction is the probability that the given value will turn up
            // on a roll.
            //
            // The events are independent, so we can combine the probabilities by summing them.
            let occ = o1 * o2;
            // This represents _only one way_ to get this value: this roll from A, this roll
            // from B.
            // Accumulate from different rolls:
            result.add_occurrences(val, occ);
        }

        debug_assert_eq!(a.total() * b.total(), result.total(), "{result:?}");

        result
    }
}

impl std::ops::Add<Distribution> for Distribution {
    type Output = Distribution;

    fn add(self, rhs: Distribution) -> Self::Output {
        (&self) + (&rhs)
    }
}

impl Neg for &Distribution {
    type Output = Distribution;

    fn neg(self) -> Self::Output {
        // The largest magnitude entry has
        let magnitude = (self.occurrence_by_value.len() - 1) as isize + self.offset;
        let occurrence_by_value = self.occurrence_by_value.iter().rev().copied().collect();
        Distribution {
            offset: -magnitude,
            occurrence_by_value,
        }
    }
}

impl Neg for Distribution {
    type Output = Distribution;

    fn neg(self) -> Self::Output {
        (&self).neg()
    }
}

impl std::iter::Sum for Distribution {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|a, b| a + b)
            .unwrap_or_else(|| Distribution::constant(0))
    }
}

impl Closed {
    /// Retrieve the distribution for the expression.
    pub fn distribution(&self) -> Result<Distribution, Error> {
        let mut eval = Evaluator::default();
        eval.eval(self)
    }
}

#[cfg(test)]
mod tests {
    use crate::parse::RawExpression;

    use super::*;

    fn distribution_of(s: &str) -> Result<Distribution, Error> {
        let raw = s.parse::<RawExpression>().unwrap();
        let closed: Closed = raw.try_into().expect("failed closure");
        closed.distribution()
    }

    #[test]
    fn no_div_zero() {
        let e = distribution_of("20 / (1d20 - 10)").unwrap_err();
        assert!(matches!(e, Error::DivideByZero(_)));
    }

    #[test]
    fn d20() {
        let d = distribution_of("d20").unwrap();

        for i in 1..=20isize {
            assert_eq!(d.probability(i), Ratio::new(1, 20));
        }

        for i in [-1, -2, -3, 0, 21, 22, 32] {
            assert_eq!(*d.probability(i).numer(), 0);
        }
    }

    #[test]
    fn d20_plus1() {
        let d = distribution_of("d20 + 1").unwrap();

        for i in 2..=21isize {
            assert_eq!(d.probability(i), Ratio::new(1, 20));
        }

        for i in [-1, -2, -3, 0, 1, 22, 22, 32] {
            assert_eq!(*d.probability(i).numer(), 0);
        }
    }

    #[test]
    fn two_d4() {
        let d = distribution_of("2d4").unwrap();

        for (v, p) in [(2, 1), (3, 2), (4, 3), (5, 4), (6, 3), (7, 2), (8, 1)] {
            assert_eq!(d.probability(v), Ratio::new(p, 16));
        }
    }

    #[test]
    fn advantage_disadvantage() {
        let a = distribution_of("2d20kh").unwrap();
        let b = distribution_of("1d20").unwrap();
        let c = distribution_of("2d20kl").unwrap();

        assert!(a.mean() > b.mean());
        assert!(b.mean() > c.mean());
    }

    #[test]
    fn stat_roll() {
        let stat = distribution_of("4d6kh3").unwrap();
        let diff = stat.mean() - 12.25;

        assert!(diff < 0.01, "{}", stat.mean());
    }

    #[test]
    fn require_positive_roll_count() {
        for expr in ["(1d3-2)d4", "(-1)d10"] {
            let e = distribution_of(expr).unwrap_err();
            assert!(matches!(e, Error::NegativeCount(_)));
        }
    }

    #[test]
    fn require_dice_to_keep() {
        for expr in ["2d4kh3", "(1d4)(4)kl2"] {
            let e = distribution_of(expr).unwrap_err();
            assert!(matches!(e, Error::KeepTooFew(..)));
        }
    }

    #[test]
    fn negative_modifier() {
        let d = distribution_of("1d4 + -1").unwrap();
        for i in 0..3isize {
            assert_eq!(d.probability(i), Ratio::new(1, 4));
        }
    }

    #[test]
    fn negative_die() {
        let d = -Distribution::die(4) + Distribution::constant(1);
        for i in -3..=0isize {
            assert_eq!(d.probability(i), Ratio::new(1, 4), "{d:?}");
        }
    }

    #[test]
    fn product() {
        let d = distribution_of("1d4 * 3").unwrap();
        let ps: Vec<_> = d.occurrences().collect();
        assert_eq!(&ps, &vec![(3, 1), (6, 1), (9, 1), (12, 1)])
    }

    #[test]
    fn never() {
        distribution_of("0d3").unwrap_err();
    }

    //#[test]
    //fn compare_constant() {
    //    let d = distribution_of("1d20").unwrap();
    //
    //    {
    //        // 10 > 1d20 : 9 times
    //        let d = ComparisonOp::Gt.compare(10, &d);
    //        assert_eq!(d, 9);
    //    }
    //    {
    //        let d = ComparisonOp::Ge.compare(10, &d);
    //        assert_eq!(d, 10);
    //    }
    //    {
    //        let d = ComparisonOp::Eq.compare(20, &d);
    //        assert_eq!(d, 1);
    //    }
    //    {
    //        let d = ComparisonOp::Eq.compare(21, &d);
    //        assert_eq!(d, 0);
    //    }
    //    {
    //        // 0 <= 1d20 always
    //        let d = ComparisonOp::Le.compare(00, &d);
    //        assert_eq!(d, 20);
    //    }
    //    {
    //        let d = ComparisonOp::Le.compare(18, &d);
    //        assert_eq!(d, 3);
    //    }
    //    {
    //        let d = ComparisonOp::Lt.compare(3, &d);
    //        assert_eq!(d, 17);
    //    }
    //}

    #[test]
    fn critical_slap() {
        let d = distribution_of(
            r#"
        [ATK: 1d20] (ATK >= 12) * 1 + (ATK = 20) * 1
    "#,
        )
        .unwrap();
        let ps: Vec<_> = d.occurrences().collect();
        assert_eq!(&ps, &vec![(0, 11), (1, 8), (2, 1)])
    }

    #[test]
    fn critical_fail() {
        let d = distribution_of(
            r#"
        [ATK: 1d20] (ATK > 1) * (1 + (ATK = 20) * 1)
        "#,
        )
        .unwrap();
        let ps: Vec<_> = d.occurrences().collect();
        assert_eq!(&ps, &vec![(0, 1), (1, 18), (2, 1)])
    }

    #[test]
    fn even_contest() {
        let d = distribution_of(
            r#"
            (1d20 = 1d20) * 2
        "#,
        )
        .unwrap();
        let ps: Vec<_> = d.occurrences().collect();
        assert_eq!(&ps, &vec![(0, 380), (2, 20)])
    }

    #[test]
    fn break_even_contest() {
        let d = distribution_of(
            r#"
            (1d20 >= 1d20) * 2
        "#,
        )
        .unwrap();
        let ps: Vec<_> = d.occurrences().collect();
        // >= is slightly biased towards the aggressor, "meets or exceeds"
        assert_eq!(&ps, &vec![(0, 190), (2, 210)])
    }

    #[test]
    fn dagger() {
        let d = distribution_of("[ATK: 1d20] (ATK > 10) * 1d4").unwrap();
        let ps: Vec<_> = d.occurrences().collect();
        // In 10/20 cases, we pick the first branch.
        // In 10/20 cases, we pick the second branch.
        // In the second branch, we get each value 1/4 of the time.

        assert_eq!(&ps, &vec![(0, 40), (1, 10), (2, 10), (3, 10), (4, 10)])
    }

    #[test]
    fn floor_div() {
        let d = distribution_of("1d4 / 2").unwrap();
        let ps: Vec<_> = d.occurrences().collect();
        assert_eq!(&ps, &vec![(0, 1), (1, 2), (2, 1)])
    }
}
