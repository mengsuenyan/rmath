
/// RoundingMode determines how a Float value is rounded to the
/// desired precision
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum RoundingMode {
    /// IEEE 754-2008 roundTiesToEven
    ToNearestEven,
    /// IEEE 754-2008 roundTiesToAway
    ToNearestAway,
    /// IEEE 754-2008 roundTowardZero
    ToZero,
    /// no IEEE 754-2008 equivalent
    AwayFromZero,
    /// IEEE 754-2008 roundTowardNegative
    ToNegativeInf,
    /// IEEE 754-2008 roundTowardPositive
    ToPositiveInf,
}

/// Accuracy describes the rounding error produced by the most recent  
/// operation that generated a Float value, relative to the exact value.
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Accuracy {
    Below,
    Exact,
    Above,
}

/// Internal representation: The mantissa bits x.mant of a nonzero finite
/// Float x are stored in a nat slice long enough to hold up to x.prec bits;
/// the slice may (but doesn't have to) be shorter if the mantissa contains
/// trailing 0 bits. x.mant is normalized if the msb of x.mant == 1 (i.e.,
/// the msb is shifted all the way "to the left"). Thus, if the mantissa has
/// trailing 0 bits or x.prec is not a multiple of the Word size _W,
/// x.mant[0] has trailing zero bits. The msb of the mantissa corresponds
/// to the value 0.5; the exponent x.exp shifts the binary point as needed.
///
/// A zero or non-finite Float x ignores x.mant and x.exp.
///
/// x                 form      neg      mant         exp
/// ----------------------------------------------------------
/// ±0                zero      sign     -            -
/// 0 < |x| < +Inf    finite    sign     mantissa     exponent
/// ±Inf              inf       sign     -            -
/// A form value describes the internal representation.
/// The form value order is relevant - do not change!
#[derive(Copy, Clone, PartialEq, Eq)]
pub(super) enum Form {
    Zero,
    Finite,
    Inf,
    Nan,
}



impl Form {
    #[inline]
    pub(super) fn is_finite(self) -> bool {
        self == Self::Finite
    }

    #[inline]
    pub(super) fn is_zero(self) -> bool {
        self == Self::Zero
    }

    #[inline]
    pub(super) fn is_infinite(self) -> bool {
        self == Self::Inf
    }

    #[inline]
    pub(super) fn is_nan(self) -> bool {
        self == Self::Nan
    }
}
