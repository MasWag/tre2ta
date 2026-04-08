//! `tre2ta` translates timed regular expressions (TREs) into timed automata (TAs).
//!
//! The crate exposes:
//! - [`TimedRegex`] and [`Interval`] for TRE syntax,
//! - [`TimedAutomaton`] and related types for the target automaton model,
//! - [`parse`] and [`parse_with`] for the current textual TRE syntax,
//! - [`translate()`] for the TRE-to-TA construction, and
//! - [`to_dot`] and [`to_jani`] for Graphviz DOT and JANI export.
//!
//! A typical workflow is:
//! 1. parse a textual TRE with [`parse`] or [`parse_with`],
//! 2. translate it with [`translate()`], which validates the expression and
//!    trims dead states from the resulting automaton,
//! 3. export the automaton with [`to_dot`] or [`to_jani`].
//!
//! When constructing syntax trees or automata manually, prefer checked
//! constructors such as [`Interval::new`] and [`TimedAutomaton::new`]. If you
//! build values directly through public fields, call [`TimedRegex::validate`]
//! or [`TimedAutomaton::validate`] before treating them as trusted inputs.

use std::{convert::Infallible, fmt::Display};

pub mod dot;
pub mod error;
pub mod jani;
pub mod ta;
pub mod translate;
pub mod tre;

lalrpop_util::lalrpop_mod!(
    #[doc = "Generated LALRPOP parser for the crate's textual TRE syntax."]
    #[doc = ""]
    #[doc = "Most users should prefer the higher-level [`parse`] helper."]
    pub parser
);

pub use dot::to_dot;
pub use error::Error;
pub use jani::to_jani;
pub use ta::{ClockConstraint, Location, TimedAutomaton, Transition};
pub use translate::{LabelIntersect, translate};
pub use tre::{Interval, TimedRegex};

/// Parse a textual timed regular expression into the crate's AST using a
/// caller-supplied atom parser.
///
/// This keeps the textual frontend reusable while the core AST remains generic
/// over label type.
///
/// # Errors
///
/// Returns [`Error::Parse`] when `input` does not match the supported TRE
/// grammar or when `parse_label` rejects an atom. Returns
/// [`Error::InvalidInterval`] when the parsed expression contains an
/// inconsistent timing interval.
///
/// # Examples
///
/// ```
/// use tre2ta::{TimedRegex, parse_with};
///
/// #[derive(Clone, Debug, PartialEq, Eq)]
/// enum Label {
///     A,
///     B,
/// }
///
/// let expr = parse_with("a ; b", |atom| match atom {
///     "a" => Ok(Label::A),
///     "b" => Ok(Label::B),
///     _ => Err("unknown label"),
/// })?;
///
/// assert_eq!(expr, TimedRegex::Concat(
///     Box::new(TimedRegex::Atom(Label::A)),
///     Box::new(TimedRegex::Atom(Label::B)),
/// ));
/// # Ok::<(), tre2ta::Error>(())
/// ```
pub fn parse_with<L, F, E>(input: &str, parse_label: F) -> Result<TimedRegex<L>, Error>
where
    F: for<'a> FnMut(&'a str) -> Result<L, E>,
    E: Display,
{
    let mut label_parser = parse_label;
    let mut parse_atom =
        |atom: &str| label_parser(atom).map_err(|error| format!("invalid atom {atom:?}: {error}"));

    let expr = parser::RegexParser::new()
        .parse(&mut parse_atom, input)
        .map_err(|e| Error::Parse(e.to_string()))?;
    expr.validate()?;
    Ok(expr)
}

/// Parse a textual timed regular expression into the crate's AST using
/// [`String`] atoms.
///
/// This is a convenience wrapper around [`parse_with`] for the default textual
/// frontend.
///
/// # Errors
///
/// Returns [`Error::Parse`] when `input` does not match the supported TRE
/// grammar. Returns [`Error::InvalidInterval`] when the parsed expression
/// contains an inconsistent timing interval.
///
/// # Examples
///
/// ```
/// use tre2ta::{TimedRegex, parse};
///
/// assert_eq!(parse("a ; b")?, TimedRegex::Concat(
///     Box::new(TimedRegex::Atom("a".to_string())),
///     Box::new(TimedRegex::Atom("b".to_string())),
/// ));
/// # Ok::<(), tre2ta::Error>(())
/// ```
pub fn parse(input: &str) -> Result<TimedRegex<String>, Error> {
    parse_with::<String, _, Infallible>(input, |atom| Ok(atom.to_owned()))
}
