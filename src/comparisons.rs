use crate::traits::Abs;
use fixnum::ops::{Bounded, CheckedAdd, One, RoundMode, RoundingMul, Zero};
use fixnum::{FixedPoint, Precision};
use thiserror::Error;

#[derive(Error, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub enum ApproxEqError<F> {
    #[error("Expected absolute tolerance to be non-negative, got {0:?}")]
    NegativeAbsoluteTolerance(F),
    #[error("Expected percentage to be in interval [0, 1), got {0:?}")]
    IncorrectRelativePercentage(F),
}

#[inline]
fn are_approx_eq_abs_unchecked<F>(left: F, right: F, tolerance: F) -> bool
where
    F: Ord + Zero + CheckedAdd<Output = F> + Bounded + Clone,
{
    left.clone() <= right.clone().saturating_add(tolerance.clone())
        && right <= left.saturating_add(tolerance)
}

/// Calculate if two values are approximately equal
/// up to some absolute tolerance (constant value)
pub fn are_approx_eq_abs<F>(left: F, right: F, tolerance: F) -> Result<bool, ApproxEqError<F>>
where
    F: Ord + Zero + CheckedAdd<Output = F> + Bounded + Clone,
{
    if tolerance >= F::ZERO {
        Ok(are_approx_eq_abs_unchecked(left, right, tolerance))
    } else {
        Err(ApproxEqError::NegativeAbsoluteTolerance(tolerance))
    }
}

/// Calculate relative absolute tolerance for two numbers: percentage of their magnitude
/// `a.abs() + b.abs()`
fn calculate_relative_tolerance<I, P>(
    a: FixedPoint<I, P>,
    b: FixedPoint<I, P>,
    percentage: FixedPoint<I, P>,
) -> Result<FixedPoint<I, P>, ApproxEqError<FixedPoint<I, P>>>
where
    I: Ord + From<i16>,
    P: Precision + Ord,
    FixedPoint<I, P>: Zero
        + One
        + Abs
        + Bounded
        + CheckedAdd<Output = FixedPoint<I, P>>
        + RoundingMul<Output = FixedPoint<I, P>>,
{
    let percentage_correct =
        percentage >= FixedPoint::<I, P>::ZERO && percentage < FixedPoint::<I, P>::ONE;
    if !percentage_correct {
        return Err(ApproxEqError::IncorrectRelativePercentage(percentage));
    }

    let magnitude = a
        .trait_abs()
        .unwrap_or(FixedPoint::<I, P>::MAX)
        .saturating_add(b.trait_abs().unwrap_or(FixedPoint::<I, P>::MAX));
    // should not saturate as tolerance is in [0, 1)
    Ok(magnitude.saturating_rmul(percentage, RoundMode::Ceil))
}

/// Calculate if two values are approximately equal
/// up to some relative tolerance (percentage of their magnitude `a.abs() + b.abs()`)
pub fn are_approx_eq_rel<I, P>(
    left: FixedPoint<I, P>,
    right: FixedPoint<I, P>,
    percentage: FixedPoint<I, P>,
) -> Result<bool, ApproxEqError<FixedPoint<I, P>>>
where
    I: Ord + From<i16>,
    P: Precision + Ord,
    FixedPoint<I, P>: Zero
        + One
        + Abs
        + Bounded
        + Clone
        + CheckedAdd<Output = FixedPoint<I, P>>
        + RoundingMul<Output = FixedPoint<I, P>>,
{
    let tolerance = calculate_relative_tolerance(left.clone(), right.clone(), percentage)?;
    are_approx_eq_abs(left, right, tolerance)
}

/// Determine if two numbers `left` and `right` are equal up to some tolerance.
///
/// ## Tolerance
/// Both relative and absolute tolerances are considered here.
///
/// Absolute tolerance is a constant `A > 0`. `left` is approx equal to `right` if
/// `left + a = right` for some `-A <= a <= A`.
///
/// Relative tolerance for two numbers (`R > 0`) is calculated as percentage of their magnitude
/// (`M = left.abs() + right.abs()`). So `left` is approx equal to `right` if
/// `left + r = right` for some `-M*R <= r <= M*R`.
///
/// Satisfying any of the tolerances is enough to consider the numbers approximately equal.
pub fn are_approx_eq<I, P>(
    left: FixedPoint<I, P>,
    right: FixedPoint<I, P>,
    absolute_tolerance: FixedPoint<I, P>,
    relative_percentage: FixedPoint<I, P>,
) -> Result<bool, ApproxEqError<FixedPoint<I, P>>>
where
    I: Ord + From<i16>,
    P: Precision + Ord,
    FixedPoint<I, P>: Zero
        + One
        + Abs
        + Bounded
        + Clone
        + CheckedAdd<Output = FixedPoint<I, P>>
        + RoundingMul<Output = FixedPoint<I, P>>,
{
    let relative_tolerance =
        calculate_relative_tolerance(left.clone(), right.clone(), relative_percentage)?;
    // `max` may overshadow incorrect argument, so we need to check it here as well
    if absolute_tolerance >= FixedPoint::<I, P>::ZERO {
        Ok(are_approx_eq_abs_unchecked(
            left,
            right,
            absolute_tolerance.max(relative_tolerance),
        ))
    } else {
        Err(ApproxEqError::NegativeAbsoluteTolerance(absolute_tolerance))
    }
}

#[cfg(test)]
mod test {
    use super::{are_approx_eq, are_approx_eq_abs, are_approx_eq_rel, ApproxEqError};
    use fixnum::ops::{Bounded, CheckedSub, One, Zero};
    use fixnum::typenum::U18;
    use fixnum::{fixnum_const, FixedPoint};

    type CustomPrecision = U18;

    #[test]
    fn should_approx_eq_equalize_exact_numbers() {
        for number in [
            FixedPoint::<i128, CustomPrecision>::ZERO,
            FixedPoint::<i128, CustomPrecision>::MAX,
            FixedPoint::<i128, CustomPrecision>::MIN,
            FixedPoint::<i128, CustomPrecision>::from_bits(1),
            FixedPoint::<i128, CustomPrecision>::from_bits(-1),
        ] {
            assert!(are_approx_eq(
                number,
                number,
                FixedPoint::<i128, CustomPrecision>::ZERO,
                FixedPoint::<i128, CustomPrecision>::ZERO
            )
            .unwrap());
            // almost zero
            assert!(are_approx_eq(
                number,
                number,
                FixedPoint::<i128, CustomPrecision>::from_bits(1),
                FixedPoint::<i128, CustomPrecision>::ZERO
            )
            .unwrap());
            assert!(are_approx_eq(
                number,
                number,
                FixedPoint::<i128, CustomPrecision>::ZERO,
                FixedPoint::<i128, CustomPrecision>::from_bits(1)
            )
            .unwrap());
            assert!(are_approx_eq(
                number,
                number,
                FixedPoint::<i128, CustomPrecision>::from_bits(1),
                FixedPoint::<i128, CustomPrecision>::from_bits(1)
            )
            .unwrap());
            // max values
            assert!(are_approx_eq(
                number,
                number,
                FixedPoint::<i128, CustomPrecision>::MAX,
                FixedPoint::<i128, CustomPrecision>::ZERO
            )
            .unwrap());
            assert!(are_approx_eq(
                number,
                number,
                FixedPoint::<i128, CustomPrecision>::ZERO,
                FixedPoint::<i128, CustomPrecision>::ONE
                    .csub(FixedPoint::<i128, CustomPrecision>::from_bits(1))
                    .unwrap()
            )
            .unwrap());
            assert!(are_approx_eq(
                number,
                number,
                FixedPoint::<i128, CustomPrecision>::MAX,
                FixedPoint::<i128, CustomPrecision>::ONE
                    .csub(FixedPoint::from_bits(1))
                    .unwrap()
            )
            .unwrap());
        }
    }

    #[test]
    fn should_approx_eq_abs_equalize_exact_numbers() {
        for number in [
            FixedPoint::<i128, CustomPrecision>::ZERO,
            FixedPoint::<i128, CustomPrecision>::MAX,
            FixedPoint::<i128, CustomPrecision>::MIN,
            FixedPoint::<i128, CustomPrecision>::from_bits(1),
            FixedPoint::<i128, CustomPrecision>::from_bits(-1),
        ] {
            assert!(
                are_approx_eq_abs(number, number, FixedPoint::<i128, CustomPrecision>::ZERO)
                    .unwrap()
            );
            assert!(are_approx_eq_abs(
                number,
                number,
                FixedPoint::<i128, CustomPrecision>::from_bits(1)
            )
            .unwrap());
            assert!(
                are_approx_eq_abs(number, number, FixedPoint::<i128, CustomPrecision>::MAX)
                    .unwrap()
            );
        }
    }

    #[test]
    fn should_approx_eq_rel_equalize_exact_numbers() {
        for number in [
            FixedPoint::<i128, CustomPrecision>::ZERO,
            FixedPoint::<i128, CustomPrecision>::MAX,
            FixedPoint::<i128, CustomPrecision>::MIN,
            FixedPoint::<i128, CustomPrecision>::from_bits(1),
            FixedPoint::<i128, CustomPrecision>::from_bits(-1),
        ] {
            assert!(
                are_approx_eq_rel(number, number, FixedPoint::<i128, CustomPrecision>::ZERO)
                    .unwrap()
            );
            assert!(are_approx_eq_rel(
                number,
                number,
                FixedPoint::<i128, CustomPrecision>::from_bits(1)
            )
            .unwrap());
            assert!(are_approx_eq_rel(
                number,
                number,
                FixedPoint::<i128, CustomPrecision>::ONE
                    .csub(FixedPoint::from_bits(1))
                    .unwrap()
            )
            .unwrap());
        }
    }

    // abs tolerance is drawn as (<=.=>)
    // rel tolerance is drawn as ({#.#})
    struct ApproxEqTestCase {
        left: FixedPoint<i128, CustomPrecision>,
        right: FixedPoint<i128, CustomPrecision>,
        absolute_tolerance: FixedPoint<i128, CustomPrecision>,
        relative_percentage: FixedPoint<i128, CustomPrecision>,
    }

    impl ApproxEqTestCase {
        const fn new(
            left: FixedPoint<i128, CustomPrecision>,
            right: FixedPoint<i128, CustomPrecision>,
            absolute_tolerance: FixedPoint<i128, CustomPrecision>,
            relative_percentage: FixedPoint<i128, CustomPrecision>,
        ) -> Self {
            Self {
                left,
                right,
                absolute_tolerance,
                relative_percentage,
            }
        }
    }

    // Test cases where the numbers are approx. equal only by absolute tolerance
    const APPROX_EQ_ABS_MATCH_CASES: &[ApproxEqTestCase] = &[
        // -5        0 1       5
        // |         | |       |
        // <=========.=========>
        //           ^right    ^left
        // abs tolerance: +-5
        // rel tolerance: +-0.05
        ApproxEqTestCase::new(
            fixnum_const!(5, 18),
            fixnum_const!(0, 18),
            fixnum_const!(5, 18),
            fixnum_const!(0.01, 18),
        ),
        // -5        0 1       5
        // |         | |       |
        // <=========.=========>
        // ^left     ^right
        // abs tolerance: +-5
        // rel tolerance: +-0.05
        ApproxEqTestCase::new(
            fixnum_const!(-5, 18),
            fixnum_const!(0, 18),
            fixnum_const!(5, 18),
            fixnum_const!(0.01, 18),
        ),
        // -5        0 1       5
        // |         | |       |
        // <=========.=========>
        //           ^right
        //            ^~left
        // abs tolerance: +-5
        // rel tolerance: +-0.05
        ApproxEqTestCase::new(
            FixedPoint::<i128, CustomPrecision>::from_bits(
                fixnum::_priv::parse_fixed(stringify!(0.05), fixnum::_priv::pow10(18)) + 1,
            ),
            fixnum_const!(0, 18),
            fixnum_const!(5, 18),
            fixnum_const!(0.01, 18),
        ),
        // -5        0 1       5
        // |         | |       |
        // <=========.=========>
        //           ^right
        //          ^~left
        // abs tolerance: +-5
        // rel tolerance: +-0.05
        ApproxEqTestCase::new(
            FixedPoint::<i128, CustomPrecision>::from_bits(
                -fixnum::_priv::parse_fixed(stringify!(0.05), fixnum::_priv::pow10(18)) - 1,
            ),
            fixnum_const!(0, 18),
            fixnum_const!(5, 18),
            fixnum_const!(0.01, 18),
        ),
        // 47        52        57
        // |         |         |
        // <=========.=========>
        // ^left     ^right
        // abs tolerance: +-5
        // rel tolerance: +-4.95
        ApproxEqTestCase::new(
            fixnum_const!(47, 18),
            fixnum_const!(52, 18),
            fixnum_const!(5, 18),
            fixnum_const!(0.05, 18),
        ),
        // closer to rel tolerance:
        // 47.02        51.98
        // |            |
        // <============.============>
        // ^left        ^right
        // abs tolerance: +-5
        // rel tolerance: +-4.95
        ApproxEqTestCase::new(
            fixnum_const!(47.02, 18),
            fixnum_const!(51.98, 18),
            fixnum_const!(5, 18),
            fixnum_const!(0.05, 18),
        ),
    ];

    #[test]
    fn should_approx_eq_match_abs_tolerance() {
        for &ApproxEqTestCase {
            left,
            right,
            absolute_tolerance,
            relative_percentage,
        } in APPROX_EQ_ABS_MATCH_CASES
        {
            assert!(
                are_approx_eq(left, right, absolute_tolerance, relative_percentage).unwrap(),
                "Expected {} = {} with absolute tolerance {} and relative tolerance (%) {}, but got '!='",
                left, right, absolute_tolerance, relative_percentage
            );
            assert!(
                are_approx_eq(right, left, absolute_tolerance, relative_percentage).unwrap(),
                "Expected approx eq to be symmetrical; {} = {}, but {} != {} for abs tolerance {} rel tolerance (%) {}",
                left, right, right, left, absolute_tolerance, relative_percentage
            );
        }
    }

    #[test]
    fn should_approx_eq_abs_match_abs_tolerance() {
        for &ApproxEqTestCase {
            left,
            right,
            absolute_tolerance,
            relative_percentage: _,
        } in APPROX_EQ_ABS_MATCH_CASES
        {
            assert!(
                are_approx_eq_abs(left, right, absolute_tolerance).unwrap(),
                "Expected {} = {} with absolute tolerance {}, but got '!='",
                left,
                right,
                absolute_tolerance
            );
            assert!(
                are_approx_eq_abs(right, left, absolute_tolerance).unwrap(),
                "Expected approx eq to be symmetrical; {} = {}, but {} != {} for abs tolerance {}",
                left,
                right,
                right,
                left,
                absolute_tolerance
            );
        }
    }

    #[test]
    fn should_approx_eq_rel_not_match_abs_tolerance() {
        for &ApproxEqTestCase {
            left,
            right,
            absolute_tolerance: _,
            relative_percentage,
        } in APPROX_EQ_ABS_MATCH_CASES
        {
            assert!(
                !are_approx_eq_rel(left, right, relative_percentage).unwrap(),
                "Expected {} != {} with relative tolerance (%) {}, but got '='",
                left,
                right,
                relative_percentage
            );
            assert!(
                !are_approx_eq_rel(right, left, relative_percentage).unwrap(),
                "Expected approx eq to be symmetrical; {} != {}, but {} = {} for rel tolerance (%) {}",
                left, right, right, left, relative_percentage
            );
        }
    }
    // Test cases where the numbers are approx. equal only by relative tolerance
    const APPROX_EQ_REL_MATCH_CASES: &[ApproxEqTestCase] = &[
        // 0       5 6
        // |       | |
        //       {#.#}
        //         ^right
        //           ^left
        // abs tolerance: 0
        // rel tolerance: +-1.1
        ApproxEqTestCase::new(
            fixnum_const!(6, 18),
            fixnum_const!(5, 18),
            fixnum_const!(0, 18),
            fixnum_const!(0.1, 18),
        ),
        //   9   11
        //   |   |
        // ##.###}
        //   ^right
        //       ^left
        // abs tolerance: 0
        // rel tolerance: +-2
        ApproxEqTestCase::new(
            fixnum_const!(11, 18),
            fixnum_const!(9, 18),
            fixnum_const!(0, 18),
            fixnum_const!(0.1, 18),
        ),
        //   9   11
        //   |   |
        // ##.###}
        //   ^right
        //       ^left
        // abs tolerance: +-1.9999
        // rel tolerance: +-2
        ApproxEqTestCase::new(
            fixnum_const!(11, 18),
            fixnum_const!(9, 18),
            fixnum_const!(1.9999, 18),
            fixnum_const!(0.1, 18),
        ),
        //   9   10.1
        //   |   |
        // ##.###}
        //   ^left
        //       ^right
        // abs tolerance: +-1
        // rel tolerance: +-1.91
        ApproxEqTestCase::new(
            fixnum_const!(9, 18),
            fixnum_const!(10.1, 18),
            fixnum_const!(1, 18),
            fixnum_const!(0.1, 18),
        ),
    ];

    #[test]
    fn should_approx_eq_match_rel_tolerance() {
        for &ApproxEqTestCase {
            left,
            right,
            absolute_tolerance,
            relative_percentage,
        } in APPROX_EQ_REL_MATCH_CASES
        {
            assert!(
                are_approx_eq(left, right, absolute_tolerance, relative_percentage).unwrap(),
                "Expected {} = {} with absolute tolerance {} and relative tolerance (%) {}, but got '!='",
                left, right, absolute_tolerance, relative_percentage
            );
            assert!(
                are_approx_eq(right, left, absolute_tolerance, relative_percentage).unwrap(),
                "Expected approx eq to be symmetrical; {} = {}, but {} != {} for abs tolerance {} rel tolerance (%) {}",
                left, right, right, left, absolute_tolerance, relative_percentage
            );
        }
    }

    #[test]
    fn should_approx_eq_abs_not_match_rel_tolerance() {
        for &ApproxEqTestCase {
            left,
            right,
            absolute_tolerance,
            relative_percentage: _,
        } in APPROX_EQ_REL_MATCH_CASES
        {
            assert!(
                !are_approx_eq_abs(left, right, absolute_tolerance).unwrap(),
                "Expected {} != {} with absolute tolerance {}, but got '='",
                left,
                right,
                absolute_tolerance
            );
            assert!(
                !are_approx_eq_abs(right, left, absolute_tolerance).unwrap(),
                "Expected approx eq to be symmetrical; {} != {}, but {} = {} for abs tolerance {}",
                left,
                right,
                right,
                left,
                absolute_tolerance
            );
        }
    }

    #[test]
    fn should_approx_eq_rel_match_rel_tolerance() {
        for &ApproxEqTestCase {
            left,
            right,
            absolute_tolerance: _,
            relative_percentage,
        } in APPROX_EQ_REL_MATCH_CASES
        {
            assert!(
                are_approx_eq_rel(left, right, relative_percentage).unwrap(),
                "Expected {} = {} with relative tolerance (%) {}, but got '!='",
                left,
                right,
                relative_percentage
            );
            assert!(
                are_approx_eq_rel(right, left, relative_percentage).unwrap(),
                "Expected approx eq to be symmetrical; {} = {}, but {} != {} for rel tolerance (%) {}",
                left, right, right, left, relative_percentage
            );
        }
    }

    // Test cases where the numbers are not approx. equal
    const APPROX_EQ_BOTH_MATCH_CASES: &[ApproxEqTestCase] = &[
        // 0       5 6
        // |       | |
        //       {#.#}
        //         ^right
        //           ^left
        // abs tolerance: +-1.1
        // rel tolerance: +-1.1
        ApproxEqTestCase::new(
            fixnum_const!(6, 18),
            fixnum_const!(5, 18),
            fixnum_const!(1.1, 18),
            fixnum_const!(0.1, 18),
        ),
        //   9   11
        //   |   |
        // ##.###}
        //   ^left
        //       ^right
        // abs tolerance: +-2
        // rel tolerance: +-2
        ApproxEqTestCase::new(
            fixnum_const!(9, 18),
            fixnum_const!(11, 18),
            fixnum_const!(2, 18),
            fixnum_const!(0.1, 18),
        ),
        //   9      11
        //   |      |
        // ##.###}
        //    ^right
        //   ^left
        // abs tolerance: +-2
        // rel tolerance: +-2
        ApproxEqTestCase::new(
            fixnum_const!(9, 18),
            FixedPoint::<i128, CustomPrecision>::from_bits(
                fixnum::_priv::parse_fixed(stringify!(9), fixnum::_priv::pow10(18)) + 1,
            ),
            fixnum_const!(2, 18),
            fixnum_const!(0.1, 18),
        ),
        //   9   10.1
        //   |   |
        // ##.###}
        //   ^left
        //       ^right
        // abs tolerance: +-1.11
        // rel tolerance: +-1.91
        ApproxEqTestCase::new(
            fixnum_const!(9, 18),
            fixnum_const!(10.1, 18),
            fixnum_const!(1.11, 18),
            fixnum_const!(0.1, 18),
        ),
    ];

    #[test]
    fn should_approx_eq_match_both_tolerance() {
        for &ApproxEqTestCase {
            left,
            right,
            absolute_tolerance,
            relative_percentage,
        } in APPROX_EQ_BOTH_MATCH_CASES
        {
            assert!(
                are_approx_eq(left, right, absolute_tolerance, relative_percentage).unwrap(),
                "Expected {} = {} with absolute tolerance {} and relative tolerance (%) {}, but got '!='",
                left, right, absolute_tolerance, relative_percentage
            );
            assert!(
                are_approx_eq(right, left, absolute_tolerance, relative_percentage).unwrap(),
                "Expected approx eq to be symmetrical; {} = {}, but {} != {} for abs tolerance {} rel tolerance (%) {}",
                left, right, right, left, absolute_tolerance, relative_percentage
            );
        }
    }

    #[test]
    fn should_approx_eq_abs_match_both_tolerance() {
        for &ApproxEqTestCase {
            left,
            right,
            absolute_tolerance,
            relative_percentage: _,
        } in APPROX_EQ_BOTH_MATCH_CASES
        {
            assert!(
                are_approx_eq_abs(left, right, absolute_tolerance).unwrap(),
                "Expected {} = {} with absolute tolerance {}, but got '!='",
                left,
                right,
                absolute_tolerance
            );
            assert!(
                are_approx_eq_abs(right, left, absolute_tolerance).unwrap(),
                "Expected approx eq to be symmetrical; {} = {}, but {} != {} for abs tolerance {}",
                left,
                right,
                right,
                left,
                absolute_tolerance
            );
        }
    }

    #[test]
    fn should_approx_eq_rel_match_both_tolerance() {
        for &ApproxEqTestCase {
            left,
            right,
            absolute_tolerance: _,
            relative_percentage,
        } in APPROX_EQ_BOTH_MATCH_CASES
        {
            assert!(
                are_approx_eq_rel(left, right, relative_percentage).unwrap(),
                "Expected {} = {} with relative tolerance (%) {}, but got '!='",
                left,
                right,
                relative_percentage
            );
            assert!(
                are_approx_eq_rel(right, left, relative_percentage).unwrap(),
                "Expected approx eq to be symmetrical; {} = {}, but {} != {} for rel tolerance (%) {}",
                left, right, right, left, relative_percentage
            );
        }
    }

    // Test cases where the numbers are not approx. equal
    const APPROX_EQ_NOT_MATCH_CASES: &[ApproxEqTestCase] = &[
        // -5        0 1       5
        // |         | |       |
        // <=========.=========>
        //           ^right     ^left
        // abs tolerance: +-5
        // rel tolerance: +-0.05
        ApproxEqTestCase::new(
            FixedPoint::<i128, CustomPrecision>::from_bits(
                fixnum::_priv::parse_fixed(stringify!(5), fixnum::_priv::pow10(18)) + 1,
            ),
            fixnum_const!(0, 18),
            fixnum_const!(5, 18),
            fixnum_const!(0.01, 18),
        ),
        //  -5        0 1       5
        //  |         | |       |
        //  <=========.=========>
        // ^left      ^right
        // abs tolerance: +-5
        // rel tolerance: +-0.05
        ApproxEqTestCase::new(
            FixedPoint::<i128, CustomPrecision>::from_bits(
                -fixnum::_priv::parse_fixed(stringify!(5), fixnum::_priv::pow10(18)) - 1,
            ),
            fixnum_const!(0, 18),
            fixnum_const!(5, 18),
            fixnum_const!(0.01, 18),
        ),
        // -5        0 1       5
        // |         | |       |
        // <=========.=========>
        //           ^right
        // abs tolerance: +-5
        // rel tolerance: +-(0.01*FixedInner::MAX)
        ApproxEqTestCase::new(
            FixedPoint::<i128, CustomPrecision>::MAX,
            fixnum_const!(0, 18),
            fixnum_const!(5, 18),
            fixnum_const!(0.01, 18),
        ),
        // -5        0 1       5
        // |         | |       |
        // <=========.=========>
        //           ^right
        // abs tolerance: +-5
        // rel tolerance: +-(0.01*FixedInner::MIN.abs())
        ApproxEqTestCase::new(
            FixedPoint::<i128, CustomPrecision>::MIN,
            fixnum_const!(0, 18),
            fixnum_const!(5, 18),
            fixnum_const!(0.01, 18),
        ),
        //  47        52        57
        //  |         |         |
        //   <=========.=========>
        // ^left       ^right
        // abs tolerance: +-5
        // rel tolerance: +-4.95
        ApproxEqTestCase::new(
            FixedPoint::<i128, CustomPrecision>::from_bits(fixnum::_priv::parse_fixed(
                stringify!(47),
                fixnum::_priv::pow10(18) - 1,
            )),
            FixedPoint::<i128, CustomPrecision>::from_bits(fixnum::_priv::parse_fixed(
                stringify!(52),
                fixnum::_priv::pow10(18) + 1,
            )),
            fixnum_const!(5, 18),
            fixnum_const!(0.05, 18),
        ),
        //  47        53        57
        //  |         |         |
        //   <=========.=========>
        // ^left       ^right
        // abs tolerance: +-5
        // rel tolerance: +-5
        ApproxEqTestCase::new(
            FixedPoint::<i128, CustomPrecision>::from_bits(fixnum::_priv::parse_fixed(
                stringify!(47),
                fixnum::_priv::pow10(18) - 1,
            )),
            FixedPoint::<i128, CustomPrecision>::from_bits(fixnum::_priv::parse_fixed(
                stringify!(53),
                fixnum::_priv::pow10(18) + 1,
            )),
            fixnum_const!(5, 18),
            fixnum_const!(0.05, 18),
        ),
        //   9   11
        //   |   |
        // ##.###}
        //   ^left
        //        ^right
        // abs tolerance: 0
        // rel tolerance: +-2
        ApproxEqTestCase::new(
            fixnum_const!(9, 18),
            FixedPoint::<i128, CustomPrecision>::from_bits(fixnum::_priv::parse_fixed(
                stringify!(11),
                fixnum::_priv::pow10(18) + 10,
            )),
            fixnum_const!(0, 18),
            fixnum_const!(0.1, 18),
        ),
        //   9   11
        //   |   |
        // ##.###}
        //   ^left
        //        ^right
        // abs tolerance: +-1.9999
        // rel tolerance: +-2
        ApproxEqTestCase::new(
            fixnum_const!(9, 18),
            FixedPoint::<i128, CustomPrecision>::from_bits(fixnum::_priv::parse_fixed(
                stringify!(11),
                fixnum::_priv::pow10(18) + 10,
            )),
            fixnum_const!(1.9999, 18),
            fixnum_const!(0.1, 18),
        ),
    ];

    #[test]
    fn should_approx_eq_not_match() {
        for &ApproxEqTestCase {
            left,
            right,
            absolute_tolerance,
            relative_percentage,
        } in APPROX_EQ_NOT_MATCH_CASES
        {
            assert!(
                !are_approx_eq(left, right, absolute_tolerance, relative_percentage).unwrap(),
                "Expected {} != {} with absolute tolerance {} and relative tolerance (%) {}, but got '=='",
                left, right, absolute_tolerance, relative_percentage
            );
            assert!(
                !are_approx_eq(right, left, absolute_tolerance, relative_percentage).unwrap(),
                "Expected approx eq to be symmetrical; {} != {}, but {} = {} for abs tolerance {} rel tolerance (%) {}",
                left, right, right, left, absolute_tolerance, relative_percentage
            );
        }
    }

    #[test]
    fn should_fail_incorrect_relative_percentage() {
        let percentage = FixedPoint::<i128, CustomPrecision>::from_bits(-1234);
        assert_eq!(
            are_approx_eq(
                FixedPoint::<i128, CustomPrecision>::ZERO,
                FixedPoint::<i128, CustomPrecision>::ZERO,
                FixedPoint::<i128, CustomPrecision>::ZERO,
                percentage,
            ),
            Err(ApproxEqError::IncorrectRelativePercentage(percentage))
        );
        let percentage = FixedPoint::<i128, CustomPrecision>::ONE
            .csub(FixedPoint::from_bits(1))
            .unwrap();
        assert_eq!(
            are_approx_eq(
                FixedPoint::<i128, CustomPrecision>::ZERO,
                FixedPoint::<i128, CustomPrecision>::ZERO,
                FixedPoint::<i128, CustomPrecision>::ZERO,
                percentage,
            ),
            Err(ApproxEqError::IncorrectRelativePercentage(percentage))
        );
    }

    #[test]
    fn should_fail_incorrect_absolute_percentage() {
        let abs_tolerance = FixedPoint::<i128, CustomPrecision>::from_bits(-1);
        assert_eq!(
            are_approx_eq(
                FixedPoint::<i128, CustomPrecision>::ZERO,
                FixedPoint::<i128, CustomPrecision>::ZERO,
                abs_tolerance,
                FixedPoint::<i128, CustomPrecision>::ZERO,
            ),
            Err(ApproxEqError::NegativeAbsoluteTolerance(abs_tolerance))
        );
        let abs_tolerance = FixedPoint::<i128, CustomPrecision>::from_bits(i128::MIN);
        assert_eq!(
            are_approx_eq(
                FixedPoint::<i128, CustomPrecision>::ZERO,
                FixedPoint::<i128, CustomPrecision>::ZERO,
                abs_tolerance,
                FixedPoint::<i128, CustomPrecision>::ZERO,
            ),
            Err(ApproxEqError::NegativeAbsoluteTolerance(abs_tolerance))
        );
    }
}
