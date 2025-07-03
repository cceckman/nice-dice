use rand::Rng;

use crate::Dice;

/// Trait representing what expressions can be simulated (evaluated).
pub trait Simulate {
    /// Take a single sample of this expression / distribution.
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> isize;
}

impl Simulate for Dice {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> isize {
        if self.n == 0 || self.m == 0 {
            return 0;
        }

        (0..self.n)
            .map(|_| rng.random_range(1..=self.m))
            .sum::<usize>()
            .try_into()
            .expect("exceeded isize")
    }
}

/// Statistics gathered from a population of samples.
struct SampleStats {
    mean: f64,
    standard_deviation: f64,

    /// Frequency table: how often each value occurs in the population.
    /// Buckets are contiguous, starting from minimum_value.
    frequency_by_value: Vec<usize>,
    minimum_value: isize,
}

impl SampleStats {
    /// Simulate the expression to collect metrics.
    pub fn simulate_and_compute<E: Simulate, R: rand::Rng + ?Sized>(
        e: &E,
        rng: &mut R,
        samples: usize,
    ) -> SampleStats {
        // 0, 1, 2, 3, 4... index maps to value.
        let mut nonnegative: Vec<usize> = vec![0];
        // -1, -2, -3, -4... index = -value -1... the bitwise / one's complement.
        let mut negative: Vec<usize> = Vec::new();

        let mut sum: i128 = 0;

        // RNG loop first, then analyze frequency_by_value.
        for sample in (0..samples).map(|_| e.sample(rng)) {
            sum += sample as i128;
            if sample < 0 {
                // Goes in the negatives list.
                let bucket = (!sample) as usize;
                if bucket >= negative.len() {
                    negative.resize(bucket + 1, 0);
                }
                negative[bucket] += 1;
            } else {
                let bucket = sample as usize;
                if bucket >= nonnegative.len() {
                    nonnegative.resize(bucket + 1, 0);
                }
                nonnegative[bucket] += 1;
            }
        }
        let mean = (sum as f64) / (samples as f64);

        let standard_deviation = {
            let neg_samples = negative.iter().enumerate().map(|(i, &count)| {
                let value = !(i as isize) as f64;
                (value, count)
            });
            let value_counts = nonnegative
                .iter()
                .enumerate()
                .map(|(i, &count)| (i as f64, count))
                .chain(neg_samples);
            let sample_stddev_sum = value_counts
                .map(|(value, count)| {
                    // (x_i = x_bar)*2, times the number it appears as a sample
                    ((value - mean) * (value - mean)) * (count as f64)
                })
                .sum::<f64>();
            // "corrected sample standard deviation"
            (sample_stddev_sum / (samples as f64)).sqrt()
        };

        // If the negatives set is empty, the minimum value is 0; if it has length 1, the minimum
        // value is -1, etc.
        let minimum_value = -(negative.len() as isize);
        let frequency_by_value = negative.into_iter().rev().chain(nonnegative).collect();

        SampleStats {
            mean,
            standard_deviation,
            frequency_by_value,
            minimum_value,
        }
    }

    //
    ///// Compute the statistics of a sample population.
    //pub fn compute(population: &[isize]) -> PopulationStats {
    //    let mut min = 0;
    //    let mut frequency_by_value = VecDeque::new();
    //    for &value in population.iter() {
    //        while value < min {
    //            frequency_by_value.push_front(0);
    //            min -= 1;
    //        }
    //        let bucket : usize = (value - min).try_into().expect("must be a positive bucket");
    //        while frequency_by_value.len() <= bucket {
    //            frequency_by_value.push_back(0);
    //        }
    //        frequency_by_value.ins
    //    }
    //
    //
    //
    //
    //    let pop: f64 = (population.len()) as f64;
    //    let sum: f64 = population.iter().map(|v| *v as f64).sum();
    //    let mean: f64 = sum / pop;
    //
    //    let dev_squared = |v: &isize| -> f64 {
    //        let diff = (*v as f64) - mean;
    //        diff * diff
    //    };
    //
    //    let standard_deviation = f64::sqrt(population.iter().map(dev_squared).sum::<f64>() / pop);
    //
    //    PopulationStats {
    //        mean,
    //        standard_deviation,
    //    }
    //}
}

/// Analytic solutions to questions about an expression.
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
    fn expected_value(&self) -> f64;
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

    fn expected_value(&self) -> f64 {
        // Polyhedral die have a uniform probability distribution
        // from 1 to N... which means the expected value is:
        let k = (self.m - 1) as f64 / 2.0 + 1.0;
        k * (self.n as f64)
    }
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;

    use crate::{ReducedExpression, dice_notation};

    use super::*;

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

    #[test]
    fn summarize_positive_roll() {
        // Use a PRNG with a known seed; even though we're looking at "random numbers", this is
        // still a deterministic test.
        let count = 100000;
        let mut rng = rand_pcg::Pcg64::seed_from_u64(3278);
        let e: ReducedExpression = dice_notation::expression("1d20+1")
            .expect("should parse")
            .into();
        let SampleStats {
            mean: got_mean,
            standard_deviation: got_stddev,
            frequency_by_value: got_freq,
            minimum_value: got_min,
        } = SampleStats::simulate_and_compute(&e, &mut rng, count);

        assert!(
            got_min >= 0,
            "got a negative minimum for a positive distribution: {got_min}"
        );
        let mean_diff = got_mean - 11.5;
        assert!(mean_diff < 0.01, "got an incorrect mean: {got_mean}");

        // Per wikipedia, variance of the discrete uniform distribution is
        // ((b - a + 1) ** 2 - 1) / 12
        // ((21 - 2 + 1) ** 2 - 1) / 12
        // (20*2 - 1 ) / 12
        // and stddev = sqrt(variance)
        let want_stddev = ((20 * 20 - 1) as f64 / 12f64).sqrt();
        let stddiv_diff = got_stddev - want_stddev;
        assert!(
            stddiv_diff < 0.01,
            "got an incorrect stddev: got {got_stddev}, want {want_stddev}"
        );

        let got_count = got_freq.iter().sum::<usize>();
        assert_eq!(got_count, count);
    }

    #[test]
    fn summarize_negative_roll() {
        // Use a PRNG with a known seed; even though we're looking at "random numbers", this is
        // still a deterministic test.
        let count = 100000;
        let mut rng = rand_pcg::Pcg64::seed_from_u64(3278);
        let e: ReducedExpression = dice_notation::expression("1d20-1d20")
            .expect("should parse")
            .into();
        let SampleStats {
            mean: got_mean,
            standard_deviation: _,
            frequency_by_value: got_freq,
            minimum_value: got_min,
        } = SampleStats::simulate_and_compute(&e, &mut rng, count);

        assert_eq!(got_min, -19);
        let mean_diff = got_mean - 0.0;
        assert!(mean_diff < 0.01, "got an incorrect mean: {got_mean}");

        let got_count = got_freq.iter().sum::<usize>();
        assert_eq!(got_count, count);
    }
}
