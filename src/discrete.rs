//! Probability computation via discrete (integral) math and combinatorics.

use std::{collections::BTreeMap, ops::Neg};

use num::rational::Ratio;

use crate::{Dice, ReducedExpression};

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

    pub fn probability(&self, value: isize) -> Ratio<usize> {
        let index = value - self.offset;
        if (0..(self.occurrence_by_value.len() as isize)).contains(&index) {
            Ratio::new(self.occurrence_by_value[index as usize], self.total())
        } else {
            Ratio::new(0, 1)
        }
    }

    /// Report the total number of occurrences in this expression, i.e. the number of possible
    /// rolls (rather than the number of distinct values).
    pub fn total(&self) -> usize {
        self.occurrence_by_value.iter().sum()
    }

    /// Iterator over (value, occurrences) tuples in this distribution.
    pub fn occurrences(&self) -> impl Iterator<Item = (isize, usize)> + use<'_> {
        self.occurrence_by_value
            .iter()
            .enumerate()
            .map(|(index, &occurrences)| ((index as isize + self.offset), occurrences))
    }

    /// Format the distribution as an HTML table.
    pub fn html_table(&self) -> maud::PreEscaped<String> {
        let total = self.total() as f64;
        maud::html!(
            table {
                tr { th { "Value" } th { "Frequency" } }
                @for (value, occurrence) in self.occurrences() {
                    tr { td { (value) } td { (occurrence as f64 / total) } }
                }
            }
        )
    }
}

impl Default for Distribution {
    fn default() -> Self {
        Self::modifier(0)
    }
}

impl std::ops::Add<&Distribution> for &Distribution {
    type Output = Distribution;

    fn add(self, rhs: &Distribution) -> Self::Output {
        let a = self;
        let b = rhs;

        let mut values: BTreeMap<isize, usize> = BTreeMap::new();
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
                *values.entry(val).or_default() += occ;
            }
        }
        let offset = values.first_key_value().map(|(&k, _)| k).unwrap_or(0);
        let max = values.last_key_value().map(|(&k, _)| k).unwrap_or(0);
        let occurrence_by_value = (offset..=max)
            .map(|value| *values.get(&value).unwrap_or(&0))
            .collect();
        let result = Distribution {
            occurrence_by_value,
            offset,
        };

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

impl std::ops::Add<&Distribution> for Distribution {
    type Output = Distribution;

    fn add(self, rhs: &Distribution) -> Self::Output {
        (&self) + (rhs)
    }
}

impl std::ops::Add<Distribution> for &Distribution {
    type Output = Distribution;

    fn add(self, rhs: Distribution) -> Self::Output {
        self + (&rhs)
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
        iter.reduce(|a, b| a + b).unwrap_or_default()
    }
}

/// A type for which a Distribution can be computed.
pub trait Distributable {
    fn distribution(&self) -> Distribution;
}

impl Distributable for Dice {
    fn distribution(&self) -> Distribution {
        let mut sum = Distribution::modifier(0);
        let d = Distribution::die(self.m);
        for _ in 0..self.n {
            sum = &sum + &d;
        }
        sum
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one_d20() {
        let d = Distribution::die(20);

        for i in 1..=20isize {
            assert_eq!(d.probability(i), Ratio::new(1, 20));
        }

        for i in [-1, -2, -3, 0, 21, 22, 32] {
            assert_eq!(*d.probability(i).numer(), 0);
        }
    }

    #[test]
    fn one_d20_plus1() {
        let d = Distribution::die(20) + Distribution::modifier(1);

        for i in 2..=21isize {
            assert_eq!(d.probability(i), Ratio::new(1, 20));
        }

        for i in [-1, -2, -3, 0, 1, 22, 22, 32] {
            assert_eq!(*d.probability(i).numer(), 0);
        }
    }

    #[test]
    fn two_d4() {
        let d = Distribution::die(4) + Distribution::die(4);

        for (v, p) in [(2, 1), (3, 2), (4, 3), (5, 4), (6, 3), (7, 2), (8, 1)] {
            assert_eq!(d.probability(v), Ratio::new(p, 16));
        }
    }

    #[test]
    fn negative_modifier() {
        let d = Distribution::die(4) + (-Distribution::modifier(1));
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
}
