//! Timed automaton data structures used as translation output.

/// A guard comparing a clock against a constant bound.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ClockConstraint {
    /// Constrain `clock < bound`.
    LessThan {
        /// Clock index.
        clock: usize,
        /// Constant bound.
        bound: u64,
    },
    /// Constrain `clock <= bound`.
    LessEqual {
        /// Clock index.
        clock: usize,
        /// Constant bound.
        bound: u64,
    },
    /// Constrain `clock > bound`.
    GreaterThan {
        /// Clock index.
        clock: usize,
        /// Constant bound.
        bound: u64,
    },
    /// Constrain `clock >= bound`.
    GreaterEqual {
        /// Clock index.
        clock: usize,
        /// Constant bound.
        bound: u64,
    },
}

/// A timed automaton location.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Location {
    /// Stable numeric identifier of the location.
    pub id: usize,
    /// Whether the location is accepting.
    pub accepting: bool,
}

/// A labeled transition between two locations.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Transition<L> {
    /// Source location identifier.
    pub source: usize,
    /// Transition label, or `None` for an epsilon transition.
    pub label: Option<L>,
    /// Conjunctive clock guards that must hold to take the transition.
    pub guards: Vec<ClockConstraint>,
    /// Clock indices reset by the transition.
    pub resets: Vec<usize>,
    /// Target location identifier.
    pub target: usize,
}

/// A timed automaton with indexed clocks and possibly multiple initial
/// locations.
///
/// Prefer constructing values with [`Self::new`], which checks the structural
/// invariants expected by trimming and export. The fields remain public to keep
/// the automaton AST explicit, but manually assembled automata should be
/// checked with [`Self::validate`] before they are exported or otherwise
/// treated as trusted.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TimedAutomaton<L> {
    /// All locations in the automaton.
    ///
    /// The translation code maintains the invariant that `locations[id].id ==
    /// id`.
    pub locations: Vec<Location>,
    /// Identifiers of the initial locations.
    pub initial_locations: Vec<usize>,
    /// Total number of clocks referenced by guards and resets.
    pub num_clocks: usize,
    /// All transitions in the automaton.
    pub transitions: Vec<Transition<L>>,
}

impl<L> TimedAutomaton<L> {
    /// Construct a timed automaton and validate its structural invariants.
    ///
    /// # Errors
    ///
    /// Returns an error when location ids, initial states, transitions, guards,
    /// or resets are inconsistent with the automaton shape.
    pub fn new(
        locations: Vec<Location>,
        initial_locations: Vec<usize>,
        num_clocks: usize,
        transitions: Vec<Transition<L>>,
    ) -> Result<Self, crate::Error> {
        let automaton = Self {
            locations,
            initial_locations,
            num_clocks,
            transitions,
        };
        automaton.validate()?;
        Ok(automaton)
    }

    /// Validate structural invariants of the timed automaton.
    ///
    /// # Errors
    ///
    /// Returns an error when location ids, initial states, transitions, guards,
    /// or resets are inconsistent with the automaton shape.
    pub fn validate(&self) -> Result<(), crate::Error> {
        if self.locations.is_empty() {
            return Err(crate::Error::EmptyAutomaton);
        }

        for (index, location) in self.locations.iter().enumerate() {
            if location.id != index {
                return Err(crate::Error::InvalidLocationId {
                    index,
                    id: location.id,
                });
            }
        }

        for &location in &self.initial_locations {
            if location >= self.locations.len() {
                return Err(crate::Error::InvalidInitialLocation {
                    location,
                    num_locations: self.locations.len(),
                });
            }
        }

        for (transition_index, transition) in self.transitions.iter().enumerate() {
            if transition.source >= self.locations.len() {
                return Err(crate::Error::InvalidTransitionSource {
                    transition_index,
                    source_location: transition.source,
                    num_locations: self.locations.len(),
                });
            }
            if transition.target >= self.locations.len() {
                return Err(crate::Error::InvalidTransitionTarget {
                    transition_index,
                    target: transition.target,
                    num_locations: self.locations.len(),
                });
            }

            for (guard_index, guard) in transition.guards.iter().enumerate() {
                let clock = constraint_clock(guard);
                if clock >= self.num_clocks {
                    return Err(crate::Error::InvalidGuardClock {
                        transition_index,
                        guard_index,
                        clock,
                        num_clocks: self.num_clocks,
                    });
                }
            }

            for (reset_index, &clock) in transition.resets.iter().enumerate() {
                if clock >= self.num_clocks {
                    return Err(crate::Error::InvalidResetClock {
                        transition_index,
                        reset_index,
                        clock,
                        num_clocks: self.num_clocks,
                    });
                }
            }
        }

        Ok(())
    }

    /// Trim away locations and transitions that cannot reach an accepting
    /// location.
    ///
    /// Reachability is computed only on the directed graph induced by
    /// [`Self::transitions`]. This ignores timed-automata semantics such as
    /// guards, resets, and whether a transition is enabled.
    ///
    /// # Errors
    ///
    /// Returns an error when the automaton is not structurally well formed.
    pub fn trim_to_accepting(self) -> Result<Self, crate::Error> {
        self.validate()?;

        let mut predecessors = vec![Vec::new(); self.locations.len()];
        for transition in &self.transitions {
            predecessors[transition.target].push(transition.source);
        }

        let mut keep = vec![false; self.locations.len()];
        let mut stack = Vec::new();
        for (id, location) in self.locations.iter().enumerate() {
            if location.accepting {
                keep[id] = true;
                stack.push(id);
            }
        }

        while let Some(target) = stack.pop() {
            for &source in &predecessors[target] {
                if !keep[source] {
                    keep[source] = true;
                    stack.push(source);
                }
            }
        }

        if !keep.iter().any(|&reachable| reachable) {
            return Ok(Self {
                locations: vec![Location {
                    id: 0,
                    accepting: false,
                }],
                initial_locations: vec![0],
                num_clocks: self.num_clocks,
                transitions: Vec::new(),
            });
        }

        let mut old_to_new = vec![0; self.locations.len()];
        let mut locations = Vec::new();
        for (old_id, location) in self.locations.into_iter().enumerate() {
            if keep[old_id] {
                let new_id = locations.len();
                old_to_new[old_id] = new_id;
                locations.push(Location {
                    id: new_id,
                    accepting: location.accepting,
                });
            }
        }

        let initial_locations = self
            .initial_locations
            .into_iter()
            .filter(|&id| keep[id])
            .map(|id| old_to_new[id])
            .collect();

        let transitions = self
            .transitions
            .into_iter()
            .filter(|transition| keep[transition.source] && keep[transition.target])
            .map(|transition| Transition {
                source: old_to_new[transition.source],
                label: transition.label,
                guards: transition.guards,
                resets: transition.resets,
                target: old_to_new[transition.target],
            })
            .collect();

        Ok(Self {
            locations,
            initial_locations,
            num_clocks: self.num_clocks,
            transitions,
        })
    }
}

fn constraint_clock(constraint: &ClockConstraint) -> usize {
    match constraint {
        ClockConstraint::LessThan { clock, .. }
        | ClockConstraint::LessEqual { clock, .. }
        | ClockConstraint::GreaterThan { clock, .. }
        | ClockConstraint::GreaterEqual { clock, .. } => *clock,
    }
}
