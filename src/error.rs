//! Error types used by parsing and translation.

/// Error type for fallible crate operations.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// The textual TRE input could not be parsed.
    #[error("parse error: {0}")]
    Parse(String),

    /// A time interval has inconsistent bounds.
    #[error("invalid interval: lower bound {lower} exceeds upper bound {upper}")]
    InvalidInterval {
        /// Lower bound of the invalid interval.
        lower: u64,
        /// Upper bound of the invalid interval.
        upper: u64,
    },

    /// A timed automaton must contain at least one location.
    #[error("invalid timed automaton: locations cannot be empty")]
    EmptyAutomaton,

    /// A location id does not match its stable position in `locations`.
    #[error("invalid timed automaton: location at index {index} has id {id}, expected {index}")]
    InvalidLocationId {
        /// Index in `TimedAutomaton::locations`.
        index: usize,
        /// Stored location id.
        id: usize,
    },

    /// An initial location reference is out of bounds.
    #[error(
        "invalid timed automaton: initial location {location} out of bounds for {num_locations} locations"
    )]
    InvalidInitialLocation {
        /// Referenced location id.
        location: usize,
        /// Number of available locations.
        num_locations: usize,
    },

    /// A transition source location is out of bounds.
    #[error(
        "invalid timed automaton: transition {transition_index} source {source_location} out of bounds for {num_locations} locations"
    )]
    InvalidTransitionSource {
        /// Index of the invalid transition.
        transition_index: usize,
        /// Referenced source id.
        source_location: usize,
        /// Number of available locations.
        num_locations: usize,
    },

    /// A transition target location is out of bounds.
    #[error(
        "invalid timed automaton: transition {transition_index} target {target} out of bounds for {num_locations} locations"
    )]
    InvalidTransitionTarget {
        /// Index of the invalid transition.
        transition_index: usize,
        /// Referenced target id.
        target: usize,
        /// Number of available locations.
        num_locations: usize,
    },

    /// A guard references a clock outside the declared clock dimension.
    #[error(
        "invalid timed automaton: transition {transition_index} guard {guard_index} references clock {clock} but automaton has {num_clocks} clocks"
    )]
    InvalidGuardClock {
        /// Index of the invalid transition.
        transition_index: usize,
        /// Index of the invalid guard in the transition.
        guard_index: usize,
        /// Referenced clock id.
        clock: usize,
        /// Declared number of clocks.
        num_clocks: usize,
    },

    /// A reset references a clock outside the declared clock dimension.
    #[error(
        "invalid timed automaton: transition {transition_index} reset {reset_index} references clock {clock} but automaton has {num_clocks} clocks"
    )]
    InvalidResetClock {
        /// Index of the invalid transition.
        transition_index: usize,
        /// Index of the invalid reset in the transition.
        reset_index: usize,
        /// Referenced clock id.
        clock: usize,
        /// Declared number of clocks.
        num_clocks: usize,
    },

    /// Translation failed because the current construction cannot proceed.
    #[error("translation error: {0}")]
    Translation(&'static str),

    /// Export failed because the target representation cannot encode the value.
    #[error("export error: {0}")]
    Export(String),
}
