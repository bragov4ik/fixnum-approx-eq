/// Assertion that two values are approximately equal
/// up to some absolute tolerance (constant value)
#[macro_export]
macro_rules! assert_approx_eq_abs {
    ($left:expr, $right:expr, $tolerance:expr $(,)?) => {{
        assert!(
            $crate::comparisons::are_approx_eq_abs($left, $right, $tolerance).unwrap(),
            "{:?} != {:?} with absolute tolerance {:?}",
            $left,
            $right,
            $tolerance
        );
    }};
}

/// Assertion that two values are approximately equal
/// up to some relative tolerance (percentage of their magnitude `a.abs() + b.abs()`)
#[macro_export]
macro_rules! assert_approx_eq_rel {
    ($left:expr, $right:expr, $tolerance_percentage:expr $(,)?) => {{
        assert!(
            $crate::comparisons::are_approx_eq_rel($left, $right, $tolerance_percentage).unwrap(),
            "{:?} != {:?} with relative tolerance (%) {:?}",
            $left,
            $right,
            $tolerance_percentage
        );
    }};
}

/// Assertion if two numbers `left` and `right` are equal up to some tolerance.
///
/// See details in [crate::comparisons::are_approx_eq].
#[macro_export]
macro_rules! assert_approx_eq {
    ($left:expr, $right:expr, $abs_tolerance:expr, $rel_percentage:expr $(,)?) => {{
        assert!(
            $crate::comparisons::are_approx_eq($left, $right, $abs_tolerance, $rel_percentage)
                .unwrap(),
            "{:?} != {:?} with absolute tolerance {:?} and relative tolerance (%) {:?}",
            $left,
            $right,
            $abs_tolerance,
            $rel_percentage,
        );
    }};
}

#[cfg(test)]
mod tests {
    use fixnum::typenum::U18;
    use fixnum::{fixnum, FixedPoint};

    #[test]
    fn assert_approx_eq_works() {
        assert_approx_eq!(
            FixedPoint::<i128, U18>::from(fixnum!(0.99, 18)),
            FixedPoint::<i128, U18>::from(fixnum!(1.01, 18)),
            FixedPoint::<i128, U18>::from(fixnum!(0.02, 18)),
            FixedPoint::<i128, U18>::from(fixnum!(0.01, 18))
        );
        assert_approx_eq!(
            FixedPoint::<i128, U18>::from_bits(100000000000000),
            FixedPoint::<i128, U18>::from_bits(100000000000002),
            FixedPoint::<i128, U18>::from_bits(2),
            FixedPoint::<i128, U18>::from(fixnum!(0.0000000000001, 18)),
        );
        assert_approx_eq!(
            FixedPoint::<i128, U18>::try_from(49f64).unwrap(),
            FixedPoint::<i128, U18>::try_from(51f64).unwrap(),
            FixedPoint::<i128, U18>::try_from(2.01f64).unwrap(),
            FixedPoint::<i128, U18>::try_from(0.02f64).unwrap()
        );
    }

    #[test]
    #[should_panic]
    fn assert_approx_eq_fails_u128() {
        assert_approx_eq!(
            FixedPoint::<i128, U18>::from(fixnum!(0.99, 18)),
            FixedPoint::<i128, U18>::from(fixnum!(1.01001, 18)),
            FixedPoint::<i128, U18>::from(fixnum!(0.02, 18)),
            FixedPoint::<i128, U18>::from(fixnum!(0.01, 18))
        );
    }

    #[test]
    #[should_panic]
    fn assert_approx_eq_fails_fixed() {
        assert_approx_eq!(
            FixedPoint::<i128, U18>::from_bits(100000000000000),
            FixedPoint::<i128, U18>::from_bits(100000000000003),
            FixedPoint::<i128, U18>::from_bits(2),
            FixedPoint::<i128, U18>::from(fixnum!(0.000000000000005, 18)),
        );
    }

    #[test]
    #[should_panic]
    fn assert_approx_eq_fails_f64() {
        // both fail
        assert_approx_eq!(
            FixedPoint::<i128, U18>::try_from(49f64).unwrap(),
            FixedPoint::<i128, U18>::try_from(51.1f64).unwrap(),
            FixedPoint::<i128, U18>::try_from(2f64).unwrap(),
            FixedPoint::<i128, U18>::try_from(0.02f64).unwrap()
        );
    }

    #[test]
    fn assert_approx_eq_abs_works() {
        assert_approx_eq_abs!(
            FixedPoint::<i128, U18>::from(fixnum!(0.99, 18)),
            FixedPoint::<i128, U18>::from(fixnum!(1.01, 18)),
            FixedPoint::<i128, U18>::from(fixnum!(0.02, 18))
        );
        assert_approx_eq_abs!(
            FixedPoint::<i128, U18>::from_bits(100000000000000),
            FixedPoint::<i128, U18>::from_bits(100000000000002),
            FixedPoint::<i128, U18>::from_bits(2),
        );
        assert_approx_eq_abs!(
            FixedPoint::<i128, U18>::try_from(49f64).unwrap(),
            FixedPoint::<i128, U18>::try_from(51f64).unwrap(),
            FixedPoint::<i128, U18>::try_from(2.01f64).unwrap()
        );
    }

    #[test]
    fn assert_approx_eq_rel_works() {
        assert_approx_eq_rel!(
            FixedPoint::<i128, U18>::from(fixnum!(0.99, 18)),
            FixedPoint::<i128, U18>::from(fixnum!(1.01, 18)),
            FixedPoint::<i128, U18>::from(fixnum!(0.01, 18))
        );
        assert_approx_eq_rel!(
            FixedPoint::<i128, U18>::from_bits(100000000000000),
            FixedPoint::<i128, U18>::from_bits(100000000000002),
            FixedPoint::<i128, U18>::from(fixnum!(0.0000000000001, 18)),
        );
        assert_approx_eq_rel!(
            FixedPoint::<i128, U18>::try_from(49f64).unwrap(),
            FixedPoint::<i128, U18>::try_from(51f64).unwrap(),
            FixedPoint::<i128, U18>::try_from(0.02f64).unwrap()
        );
    }
}
