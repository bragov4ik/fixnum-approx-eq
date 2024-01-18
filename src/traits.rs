use fixnum::{ArithmeticError, FixedPoint};

pub trait Abs: Sized {
    fn abs(self) -> Result<Self, fixnum::ArithmeticError>;
}

macro_rules! impl_abs {
    ($inner:ty) => {
        impl<P> Abs for FixedPoint<$inner, P> {
            fn abs(self) -> Result<Self, ArithmeticError> {
                self.abs()
            }
        }
    };
}

impl_abs!(i16);
impl_abs!(i32);
impl_abs!(i64);
impl_abs!(i128);
