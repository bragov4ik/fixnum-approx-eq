use fixnum::{ArithmeticError, FixedPoint};

pub trait Abs: Sized {
    fn abs(self) -> Result<Self, fixnum::ArithmeticError>;
}

macro_rules! impl_abs {
    ($inner:ty) => {
        impl<P> Abs for FixedPoint<$inner, P> {
            fn abs(self) -> Result<Self, ArithmeticError> {
                FixedPoint::<$inner, P>::abs(self)
            }
        }
    };
}

impl<P> Abs for FixedPoint<i16, P> {
    fn abs(self) -> Result<Self, ArithmeticError> {
        FixedPoint::<i16, P>::abs(self)
    }
}
// impl_abs!(i16);
impl_abs!(i32);
impl_abs!(i64);
impl_abs!(i128);

#[cfg(test)]
mod tests {
    use crate::traits::Abs;
    use fixnum::typenum::U18;
    use fixnum::FixedPoint;

    #[test]
    fn abs_works() {
        let f = FixedPoint::<i16, U18>::from_decimal(-12, -2).unwrap();
        dbg!(&f);
        let f_abs = <FixedPoint<i16, U18> as Abs>::abs(f).unwrap();
        dbg!(&f_abs);
    }
}
