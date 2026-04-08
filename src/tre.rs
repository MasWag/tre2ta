//! Timed regular expression syntax tree definitions.

/// A numeric time interval used by TRE timing modifiers.
///
/// The interval may be bounded or unbounded above. Inclusivity of the lower and
/// upper bounds is tracked explicitly to support both interval syntax such as
/// `%[1, 3)` and inequality syntax such as `%(>= 5)`.
///
/// Prefer constructing intervals with [`Self::new`], [`Self::closed`], or
/// [`Self::left_closed_right_open`]. The fields remain public to keep the AST
/// explicit, but manually constructed intervals should be checked with
/// [`Self::validate`] before use.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Interval {
    /// Lower numeric bound.
    pub lower: u64,
    /// Upper numeric bound, or `None` for an unbounded interval.
    pub upper: Option<u64>,
    /// Whether the lower bound is included.
    pub lower_inclusive: bool,
    /// Whether the upper bound is included.
    pub upper_inclusive: bool,
}

impl Interval {
    /// Construct an interval after validating its bounds.
    ///
    /// # Errors
    ///
    /// Returns [`crate::Error::InvalidInterval`] when `lower > upper`.
    pub fn new(
        lower: u64,
        upper: Option<u64>,
        lower_inclusive: bool,
        upper_inclusive: bool,
    ) -> Result<Self, crate::Error> {
        let interval = Self {
            lower,
            upper,
            lower_inclusive,
            upper_inclusive,
        };
        interval.validate()?;
        Ok(interval)
    }

    /// Construct a closed interval `[lower, upper]`.
    ///
    /// Passing `None` for `upper` produces `[lower, inf]`.
    ///
    /// # Errors
    ///
    /// Returns [`crate::Error::InvalidInterval`] when `lower > upper`.
    pub fn closed(lower: u64, upper: Option<u64>) -> Result<Self, crate::Error> {
        Self::new(lower, upper, true, true)
    }

    /// Construct a left-closed, right-open interval `[lower, upper)`.
    ///
    /// Passing `None` for `upper` produces `[lower, inf)`.
    ///
    /// # Errors
    ///
    /// Returns [`crate::Error::InvalidInterval`] when `lower > upper`.
    pub fn left_closed_right_open(lower: u64, upper: Option<u64>) -> Result<Self, crate::Error> {
        Self::new(lower, upper, true, false)
    }

    /// Validate that the interval bounds are internally consistent.
    ///
    /// # Errors
    ///
    /// Returns [`crate::Error::InvalidInterval`] when both bounds are present
    /// and the lower bound is numerically greater than the upper bound.
    pub fn validate(&self) -> Result<(), crate::Error> {
        if let Some(upper) = self.upper {
            if self.lower > upper {
                return Err(crate::Error::InvalidInterval {
                    lower: self.lower,
                    upper,
                });
            }
        }
        Ok(())
    }
}

/// A timed regular expression over labels of type `L`.
///
/// The core AST stays generic in the label type so the library can be reused
/// with richer symbolic alphabets than plain strings.
///
/// Expressions built through the parser are validated automatically. If you
/// assemble a TRE manually, call [`Self::validate`] before translation so
/// malformed timing modifiers are rejected early.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TimedRegex<L> {
    /// The empty language.
    Empty,
    /// The language containing only the empty word.
    Epsilon,
    /// A single atomic label.
    Atom(L),
    /// Union of two expressions.
    Union(Box<Self>, Box<Self>),
    /// Intersection of two expressions.
    Intersection(Box<Self>, Box<Self>),
    /// Concatenation of two expressions.
    Concat(Box<Self>, Box<Self>),
    /// Zero or more repetitions of an expression.
    KleeneStar(Box<Self>),
    /// One or more repetitions of an expression.
    KleenePlus(Box<Self>),
    /// Restrict an expression to runs whose total duration lies in `Interval`.
    Within(Box<Self>, Interval),
}

impl<L> TimedRegex<L> {
    /// Validate semantic invariants of the expression tree.
    ///
    /// # Errors
    ///
    /// Returns [`crate::Error::InvalidInterval`] when a timing modifier
    /// contains inconsistent bounds.
    pub fn validate(&self) -> Result<(), crate::Error> {
        match self {
            Self::Empty | Self::Epsilon | Self::Atom(_) => Ok(()),
            Self::Union(left, right)
            | Self::Intersection(left, right)
            | Self::Concat(left, right) => {
                left.validate()?;
                right.validate()
            }
            Self::KleeneStar(expr) | Self::KleenePlus(expr) => expr.validate(),
            Self::Within(expr, interval) => {
                expr.validate()?;
                interval.validate()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interval_closed_constructor_sets_inclusive_bounds() {
        let interval = Interval::closed(2, Some(5)).unwrap();

        assert_eq!(
            interval,
            Interval {
                lower: 2,
                upper: Some(5),
                lower_inclusive: true,
                upper_inclusive: true,
            }
        );
    }

    #[test]
    fn interval_left_closed_right_open_constructor_sets_expected_flags() {
        let interval = Interval::left_closed_right_open(1, None).unwrap();

        assert_eq!(
            interval,
            Interval {
                lower: 1,
                upper: None,
                lower_inclusive: true,
                upper_inclusive: false,
            }
        );
    }

    #[test]
    fn interval_validate_accepts_equal_and_unbounded_ranges() {
        Interval::closed(3, Some(3)).unwrap().validate().unwrap();
        Interval::left_closed_right_open(4, None)
            .unwrap()
            .validate()
            .unwrap();
    }

    #[test]
    fn interval_validate_rejects_lower_bound_above_upper_bound() {
        let error = Interval::left_closed_right_open(5, Some(4)).unwrap_err();

        match error {
            crate::Error::InvalidInterval { lower, upper } => {
                assert_eq!(lower, 5);
                assert_eq!(upper, 4);
            }
            other => panic!("expected invalid interval error, got {other:?}"),
        }
    }

    #[test]
    fn timed_regex_validate_rejects_invalid_nested_interval() {
        let expr = TimedRegex::<String>::Within(
            Box::new(TimedRegex::Atom("a".to_string())),
            Interval {
                lower: 5,
                upper: Some(4),
                lower_inclusive: true,
                upper_inclusive: false,
            },
        );

        match expr.validate().unwrap_err() {
            crate::Error::InvalidInterval { lower, upper } => {
                assert_eq!(lower, 5);
                assert_eq!(upper, 4);
            }
            other => panic!("expected invalid interval error, got {other:?}"),
        }
    }
}
