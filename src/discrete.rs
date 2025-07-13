//! Probability computation via discrete (integral) math and combinatorics.

use std::ops::Neg;

use itertools::Itertools;
use num::{ToPrimitive, rational::Ratio};

use crate::{Branch, ComparisonOp, Error, Ranker, parse::Expression};

/// A computed distribution for a bounded dice expression.
/// ("bounded": does not support exploding dice.)
///
/// The default distribution has probability 1 of producing the value 0.
///
/// Addition of distributions represents the distribution that would result from summing the
/// underlying events. Negation of a distribution
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Distribution {
    /// We track probabilities of each value using integers;
    /// all of these have an implied denominator of occurrence_by_value.sum().
    occurrence_by_value: Vec<usize>,
    /// Index i in occurrence_by_value represents the number of occurrences of (i+offset).
    offset: isize,
}

impl Distribution {
    /// Generate a uniform distribution on the closed interval `[1, size]`;
    /// i.e. the distribution for rolling a die with the given number of faces.
    pub fn die(size: usize) -> Distribution {
        let mut v = Vec::new();
        v.resize(size, 1);
        Distribution {
            occurrence_by_value: v,
            offset: 1,
        }
    }

    /// Generate a "modifier" distribution, which has probability 1 of producing the given value.
    pub fn modifier(value: isize) -> Distribution {
        Distribution {
            occurrence_by_value: vec![1],
            offset: value,
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
    pub fn clean(&mut self) {
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

        for (aval, aocc) in a.occurrences() {
            for (bval, bocc) in b.occurrences() {
                let val = aval + bval;
                // aocc and bocc each represent the numerator of a fraction, aocc/atotal and
                // bocc/btotal. That fraction is the probability that the given value will turn up
                // on a roll.
                //
                // The events are independent, so we can combine the probabilities by summing them.
                let occ = aocc * bocc;
                // This represents _only one way_ to get this value: this roll from A, this roll
                // from B.
                // Accumulate from different rolls:
                result.add_occurrences(val, occ);
            }
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
            .unwrap_or_else(|| Distribution::modifier(0))
    }
}

fn repeat(
    expression: &Expression,
    count: Distribution,
    value: Distribution,
    ranker: &Ranker,
) -> Result<Distribution, Error> {
    let mut result = Distribution::empty();
    if count.min() < 0 {
        return Err(Error::NegativeCount(expression.to_string()));
    }
    if (count.min() as usize) < ranker.count() {
        return Err(Error::KeepTooFew(expression.to_string()));
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
    let keep_count = ranker.count();

    for (count, count_frequency) in count.occurrences() {
        // Assuming this count happens this often...
        let dice = std::iter::repeat(&value)
            .map(|d| d.occurrences())
            .take(count as usize);
        for value_set in dice.multi_cartesian_product() {
            let (mut values, frequencies): (Vec<isize>, Vec<usize>) = value_set.into_iter().unzip();
            // We have to compute the overall frquency including the dice we dropped;
            // in other universes (other combinations), we'd keep them.
            let occurrences = frequencies.into_iter().product::<usize>() * count_frequency;
            let value = filter(&mut values, keep_count).iter().sum();
            result.add_occurrences(value, occurrences);
        }
    }
    Ok(result)
}

fn product(a: Distribution, b: Distribution) -> Distribution {
    let mut d = Distribution::empty();

    for ((v1, f1), (v2, f2)) in a.occurrences().cartesian_product(b.occurrences()) {
        d.add_occurrences(v1 * v2, f1 * f2);
    }
    d
}

fn floor(e: &Expression, a: Distribution, b: Distribution) -> Result<Distribution, Error> {
    if *b.probability(0).numer() != 0 {
        return Err(Error::DivideByZero(e.to_string()));
    }

    let mut d = Distribution::empty();
    for ((v1, f1), (v2, f2)) in a.occurrences().cartesian_product(b.occurrences()) {
        d.add_occurrences(v1 / v2, f1 * f2);
    }
    Ok(d)
}

fn case(target: Distribution, branches: &[Branch]) -> Result<Distribution, Error> {
    let branch_distributions: Result<Vec<_>, Error> = branches
        .iter()
        .map(
            |Branch {
                 op,
                 threshold,
                 value,
             }|
             -> Result<_, Error> {
                let threshold = threshold.distribution()?;
                let value = value.distribution()?;
                Ok((*op, threshold, value))
            },
        )
        .collect();
    let branch_distributions = branch_distributions?;

    // What possibilities are there within the branches?
    // We can account for the total number without weighting them yet.
    let branches_total: usize = branch_distributions
        .iter()
        .map(|(_, t, v)| t.total() * v.total())
        .product::<usize>();

    let mut result = Distribution::empty();
    for (target, target_occ) in target.occurrences() {
        // Weight the branch possibilities by how often we wind up with the value we're currently considering.
        let mut branches_total: usize = branches_total * target_occ;

        for (op, threshold_distr, value_distr) in &branch_distributions {
            // How many times will we take _this_ branch?
            let occurrences = op.compare(target, threshold_distr);
            let branch_total = threshold_distr.total() * value_distr.total();
            // We can count towards "this branch" all the possibilities in later branches,
            // and the weights that got us _to_ this branch.
            // But we need to weight only the times that we are _on_ this branch, like so:
            branches_total /= branch_total;
            for (v, vf) in value_distr.occurrences() {
                result.add_occurrences(v, vf * occurrences * branches_total);
            }

            // Update the results for the next branch with how often we fall through:
            let residual = (threshold_distr.total() - occurrences) * value_distr.total();
            branches_total *= residual;
        }

        // If we have any probability of "falling off the end",
        // contribute it towards a zero value.
        // No conditional here; if branches_total is 0, then we add nothing to the distribution.
        result.add_occurrences(0, branches_total);
    }
    Ok(result)
}

impl ComparisonOp {
    /// Perform a comparison against the target distribution.
    /// Returns the number of occurrences in "other" in which the comparison passes.
    fn compare(&self, value: isize, other: &Distribution) -> usize {
        let gt: usize = other
            .occurrences()
            .take_while(|(v2, _)| value > *v2)
            .map(|(_, f2)| f2)
            .sum();
        let ratio = other.probability(value);
        let eq = *ratio.numer();
        let total = other.total();
        let lt = total - (gt + eq);

        match self {
            ComparisonOp::Gt => gt,
            ComparisonOp::Ge => gt + eq,
            ComparisonOp::Eq => eq,
            ComparisonOp::Le => lt + eq,
            ComparisonOp::Lt => lt,
            ComparisonOp::True => total,
        }
    }
}

impl Expression {
    /// Retrieve the distribution for the expression.
    pub fn distribution(&self) -> Result<Distribution, Error> {
        self.distribution_internal().map(|mut v| {
            v.clean();
            v
        })
    }

    fn distribution_internal(&self) -> Result<Distribution, Error> {
        match self {
            Expression::Modifier(m) => Ok(Distribution::modifier(*m as isize)),
            Expression::Die(d) => Ok(Distribution::die(*d)),
            Expression::Negated(expression) => Ok(-(expression.distribution_internal()?)),
            Expression::Symbol(_) => todo!("symbol not implemented"),
            Expression::Binding { .. } => todo!("bindings not implemented"),
            Expression::Repeated {
                count,
                value,
                ranker,
            } => repeat(
                self,
                count.distribution_internal()?,
                value.distribution_internal()?,
                ranker,
            ),
            Expression::Product(a, b) => Ok(product(
                a.distribution_internal()?,
                b.distribution_internal()?,
            )),
            Expression::Floor(a, b) => {
                floor(self, a.distribution_internal()?, b.distribution_internal()?)
            }
            Expression::Sum(expressions) => {
                let terms: Result<Vec<_>, _> = expressions
                    .iter()
                    .map(|e| e.distribution_internal())
                    .collect();
                Ok(terms?.into_iter().sum())
            }
            Expression::Case { target, branches } => case(target.distribution()?, branches),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn distribution_of(s: &str) -> Distribution {
        s.parse::<Expression>()
            .unwrap()
            .distribution_internal()
            .unwrap()
    }

    #[test]
    fn d20() {
        let d = distribution_of("d20");

        for i in 1..=20isize {
            assert_eq!(d.probability(i), Ratio::new(1, 20));
        }

        for i in [-1, -2, -3, 0, 21, 22, 32] {
            assert_eq!(*d.probability(i).numer(), 0);
        }
    }

    #[test]
    fn d20_plus1() {
        let d = distribution_of("d20 + 1");

        for i in 2..=21isize {
            assert_eq!(d.probability(i), Ratio::new(1, 20));
        }

        for i in [-1, -2, -3, 0, 1, 22, 22, 32] {
            assert_eq!(*d.probability(i).numer(), 0);
        }
    }

    #[test]
    fn two_d4() {
        let d = distribution_of("2d4");

        for (v, p) in [(2, 1), (3, 2), (4, 3), (5, 4), (6, 3), (7, 2), (8, 1)] {
            assert_eq!(d.probability(v), Ratio::new(p, 16));
        }
    }

    #[test]
    fn advantage_disadvantage() {
        let a = distribution_of("2d20kh");
        let b = distribution_of("1d20");
        let c = distribution_of("2d20kl");

        assert!(a.mean() > b.mean());
        assert!(b.mean() > c.mean());
    }

    #[test]
    fn stat_roll() {
        let stat = distribution_of("4d6kh3");
        let diff = stat.mean() - 12.25;

        assert!(diff < 0.01, "{}", stat.mean());
    }

    #[test]
    fn require_positive_roll_count() {
        for expr in ["(1d3-2)d4", "(-1)d10"] {
            let expr: Expression = expr.parse().unwrap();
            let e = expr.distribution_internal().unwrap_err();
            assert!(matches!(e, Error::NegativeCount(_)));
        }
    }

    #[test]
    fn require_dice_to_keep() {
        for expr in ["2d4kh3", "(1d4)(4)kl2"] {
            let expr: Expression = expr.parse().unwrap();
            let e = expr.distribution_internal().unwrap_err();
            assert!(matches!(e, Error::KeepTooFew(_)));
        }
    }

    #[test]
    fn negative_modifier() {
        let d = distribution_of("1d4 + -1");
        for i in 0..3isize {
            assert_eq!(d.probability(i), Ratio::new(1, 4));
        }
    }

    #[test]
    fn negative_die() {
        let d = -Distribution::die(4) + Distribution::modifier(1);
        for i in -3..=0isize {
            assert_eq!(d.probability(i), Ratio::new(1, 4), "{d:?}");
        }
    }

    #[test]
    fn product() {
        let d = distribution_of("1d4 * 3");
        let ps: Vec<_> = d.occurrences().collect();
        assert_eq!(&ps, &vec![(3, 1), (6, 1), (9, 1), (12, 1)])
    }

    #[test]
    fn never() {
        let d = distribution_of("0d3");
        let ps: Vec<_> = d.occurrences().collect();
        assert_eq!(&ps, &vec![(0, 1)]);
    }

    #[test]
    fn compare_constant() {
        let d = distribution_of("1d20");

        {
            // 10 > 1d20 : 9 times
            let d = ComparisonOp::Gt.compare(10, &d);
            assert_eq!(d, 9);
        }
        {
            let d = ComparisonOp::Ge.compare(10, &d);
            assert_eq!(d, 10);
        }
        {
            let d = ComparisonOp::Eq.compare(20, &d);
            assert_eq!(d, 1);
        }
        {
            let d = ComparisonOp::Eq.compare(21, &d);
            assert_eq!(d, 0);
        }
        {
            // 0 <= 1d20 always
            let d = ComparisonOp::Le.compare(00, &d);
            assert_eq!(d, 20);
        }
        {
            let d = ComparisonOp::Le.compare(18, &d);
            assert_eq!(d, 3);
        }
        {
            let d = ComparisonOp::Lt.compare(3, &d);
            assert_eq!(d, 17);
        }
    }

    #[test]
    fn critical_slap() {
        let d = distribution_of(
            r#"
        (1d20) { = 20: 2 } { >= 12: 1 }
    "#,
        );
        let ps: Vec<_> = d.occurrences().collect();
        assert_eq!(&ps, &vec![(0, 11), (1, 8), (2, 1)])
    }

    #[test]
    fn critical_fail() {
        let d = distribution_of(
            r#"
                (1d20) { = 20: 2 } { = 1: 0 } { 1 }
        "#,
        );
        let ps: Vec<_> = d.occurrences().collect();
        assert_eq!(&ps, &vec![(0, 1), (1, 18), (2, 1)])
    }

    #[test]
    fn even_contest() {
        let d = distribution_of(
            r#"
                (1d20) { = 1d20: 2 }
        "#,
        );
        let ps: Vec<_> = d.occurrences().collect();
        assert_eq!(&ps, &vec![(0, 380), (2, 20)])
    }

    #[test]
    fn break_even_contest() {
        let d = distribution_of(
            r#"
                (1d20) { >= 1d20: 2 }
        "#,
        );
        let ps: Vec<_> = d.occurrences().collect();
        // >= is slightly biased towards the aggressor, "meets or exceeds"
        assert_eq!(&ps, &vec![(0, 190), (2, 210)])
    }

    #[test]
    fn dagger() {
        let d = distribution_of("(1d20) { > 10: 1d4 }");
        let ps: Vec<_> = d.occurrences().collect();
        // In 10/20 cases, we pick the first branch.
        // In 10/20 cases, we pick the second branch.
        // In the second branch, we get each value 1/4 of the time.

        assert_eq!(&ps, &vec![(0, 40), (1, 10), (2, 10), (3, 10), (4, 10)])
    }

    #[test]
    fn floor_div() {
        let d = distribution_of("1d4 /_ 2");
        let ps: Vec<_> = d.occurrences().collect();
        assert_eq!(&ps, &vec![(0, 1), (1, 2), (2, 1)])
    }
}
