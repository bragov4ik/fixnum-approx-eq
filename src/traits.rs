use fixnum::{ArithmeticError, FixedPoint, Precision};

pub trait Abs: Sized {
    fn trait_abs(self) -> Result<Self, fixnum::ArithmeticError>;
}

macro_rules! impl_abs {
    ($inner:ty) => {
        impl<P> Abs for FixedPoint<$inner, P>
        where
            P: Precision,
        {
            fn trait_abs(self) -> Result<Self, ArithmeticError> {
                self.abs()
            }
        }
    };
}

#[cfg(feature = "i16")]
impl_abs!(i16);
#[cfg(feature = "i32")]
impl_abs!(i32);
#[cfg(feature = "i64")]
impl_abs!(i64);
#[cfg(feature = "i128")]
impl_abs!(i128);

#[cfg(test)]
mod tests {
    use crate::traits::Abs;
    use fixnum::typenum::U18;
    use fixnum::FixedPoint;

    #[test]
    fn abs_works() {
        let f = FixedPoint::<i128, U18>::from_decimal(-12, -2).unwrap();
        dbg!(&f);
        let f_abs = <FixedPoint<i128, U18> as Abs>::trait_abs(f).unwrap();
        dbg!(&f_abs);
    }
}
