use crate::Dice;

/// Analytic solutions to questions about a property distribution.
pub trait Analytic {
    /// The maximum value of this expression.
    ///
    /// May not exist (e.g. exploding dice).
    fn max(&self) -> Option<isize>;

    /// The minimum value of this expression.
    ///
    /// May not exist (e.g. subtracting exploding dice).
    fn min(&self) -> Option<isize>;

    /// The expected value of this expression, i.e. the mean.
    fn expected_value(&self) -> f32;
}

impl Analytic for Dice {
    fn max(&self) -> Option<isize> {
        (self.n * self.m).try_into().ok()
    }

    fn min(&self) -> Option<isize> {
        if self.n == 0 || self.m == 0 {
            Some(0)
        } else {
            // 1 on each die.
            self.n.try_into().ok()
        }
    }

    fn expected_value(&self) -> f32 {
        // Polyhedral die have a uniform probability distribution
        // from 1 to N... which means the expected value is:
        let k = (self.m - 1) as f32 / 2.0 + 1.0;
        k * (self.n as f32)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Dice, analysis::Analytic};

    #[test]
    fn max() {
        for (dice, want) in [(Dice { n: 1, m: 20 }, 20), (Dice { n: 4, m: 10 }, 40)] {
            let got = dice.max().unwrap();
            assert_eq!(got, want);
        }
    }

    #[test]
    fn min() {
        for (dice, want) in [(Dice { n: 1, m: 20 }, 1), (Dice { n: 4, m: 10 }, 4)] {
            let got = dice.min().unwrap();
            assert_eq!(got, want);
        }
    }

    #[test]
    fn expected_values() {
        for (dice, want_ev) in [(Dice { n: 1, m: 20 }, 10.5), (Dice { n: 4, m: 10 }, 22.0)] {
            let got_ev = dice.expected_value();
            let diff = (got_ev - want_ev).abs();

            assert!(diff < 0.00001, "got: {got_ev} want: {want_ev} for: {dice}")
        }
    }
}
