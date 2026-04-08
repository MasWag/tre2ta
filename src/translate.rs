//! Translation from timed regular expressions to timed automata.

use std::collections::{BTreeMap, VecDeque};

use crate::{ClockConstraint, Error, Interval, Location, TimedAutomaton, TimedRegex, Transition};

/// Label domains that can synchronize during TRE intersection.
///
/// The TRE conjunction construction builds a product automaton and asks the
/// label domain how two transition labels combine. Returning `None` means the
/// two transitions cannot synchronize.
pub trait LabelIntersect: Clone {
    /// Compute the synchronized label for two matching transitions.
    fn intersect(&self, other: &Self) -> Option<Self>;
}

impl LabelIntersect for String {
    fn intersect(&self, other: &Self) -> Option<Self> {
        if self == other {
            Some(self.clone())
        } else {
            None
        }
    }
}

/// Translate a timed regular expression into a timed automaton.
///
/// The construction is compositional: each TRE operator is translated by
/// translating its operands and combining the resulting automata.
///
/// The public translation boundary first validates the TRE and then trims the
/// resulting automaton to locations that can reach an accepting state. This
/// means the returned automaton is a presentation-friendly, accepting-reachable
/// form of the raw construction.
///
/// # Errors
///
/// Returns an error when the expression fails validation, such as when a timing
/// restriction contains an invalid interval.
pub fn translate<L: LabelIntersect>(expr: &TimedRegex<L>) -> Result<TimedAutomaton<L>, Error> {
    expr.validate()?;

    let automaton = translate_untrimmed(expr)?;
    let automaton = automaton.trim_to_accepting()?;

    debug_assert_well_formed(&automaton);

    Ok(automaton)
}

fn translate_untrimmed<L: LabelIntersect>(
    expr: &TimedRegex<L>,
) -> Result<TimedAutomaton<L>, Error> {
    let automaton = match expr {
        TimedRegex::Empty => empty_automaton(),
        TimedRegex::Epsilon => epsilon_automaton(),
        TimedRegex::Atom(label) => atom_automaton(label.clone()),
        TimedRegex::Union(left, right) => {
            disjunction(translate_untrimmed(left)?, translate_untrimmed(right)?)
        }
        TimedRegex::Intersection(left, right) => {
            conjunction(translate_untrimmed(left)?, translate_untrimmed(right)?)
        }
        TimedRegex::Concat(left, right) => {
            concatenate(translate_untrimmed(left)?, translate_untrimmed(right)?)
        }
        TimedRegex::KleeneStar(expr) => star(translate_untrimmed(expr)?),
        TimedRegex::KleenePlus(expr) => plus(translate_untrimmed(expr)?),
        TimedRegex::Within(expr, interval) => {
            time_restriction(translate_untrimmed(expr)?, interval)?
        }
    };

    debug_assert_well_formed(&automaton);

    Ok(automaton)
}

/// Build the automaton for the empty language.
fn empty_automaton<L>() -> TimedAutomaton<L> {
    TimedAutomaton {
        locations: vec![Location {
            id: 0,
            accepting: false,
        }],
        initial_locations: vec![0],
        num_clocks: 0,
        transitions: Vec::new(),
    }
}

/// Build the automaton for the language containing only the empty word.
fn epsilon_automaton<L>() -> TimedAutomaton<L> {
    TimedAutomaton {
        locations: vec![Location {
            id: 0,
            accepting: true,
        }],
        initial_locations: vec![0],
        num_clocks: 0,
        transitions: Vec::new(),
    }
}

/// Build the single-transition automaton for an atomic label.
fn atom_automaton<L>(label: L) -> TimedAutomaton<L> {
    TimedAutomaton {
        locations: vec![
            Location {
                id: 0,
                accepting: false,
            },
            Location {
                id: 1,
                accepting: true,
            },
        ],
        initial_locations: vec![0],
        num_clocks: 0,
        transitions: vec![Transition {
            source: 0,
            label: Some(label),
            guards: Vec::new(),
            resets: Vec::new(),
            target: 1,
        }],
    }
}

/// Form the disjoint-union automaton for TRE union.
///
/// The helper keeps both sets of initial locations and offsets the right-hand
/// side location identifiers so the components do not overlap.
fn disjunction<L>(left: TimedAutomaton<L>, right: TimedAutomaton<L>) -> TimedAutomaton<L>
where
    L: Clone,
{
    let right_location_offset = left.locations.len();
    let mut locations = left.locations;
    locations.extend(right.locations.into_iter().map(|location| Location {
        id: location.id + right_location_offset,
        accepting: location.accepting,
    }));

    let mut initial_locations = left.initial_locations;
    initial_locations.extend(
        right
            .initial_locations
            .into_iter()
            .map(|id| id + right_location_offset),
    );
    normalize_ids(&mut initial_locations);

    let mut transitions = left.transitions;
    transitions.extend(
        right
            .transitions
            .into_iter()
            .map(|transition| shift_transition(&transition, right_location_offset, 0)),
    );

    let automaton = TimedAutomaton {
        locations,
        initial_locations,
        num_clocks: left.num_clocks.max(right.num_clocks),
        transitions,
    };
    debug_assert_well_formed(&automaton);
    automaton
}

/// Form the product automaton used for TRE intersection.
///
/// Locations are generated on demand from reachable pairs of source locations.
/// Two outgoing transitions synchronize only when their labels intersect.
fn conjunction<L>(left: TimedAutomaton<L>, right: TimedAutomaton<L>) -> TimedAutomaton<L>
where
    L: LabelIntersect,
{
    let left_outgoing = transitions_by_source(&left);
    let right_outgoing = transitions_by_source(&right);

    let mut locations = Vec::new();
    let mut initial_locations = Vec::new();
    let mut transitions = Vec::new();
    let mut pair_to_id = BTreeMap::<(usize, usize), usize>::new();
    let mut queue = VecDeque::new();

    for &left_initial in &left.initial_locations {
        for &right_initial in &right.initial_locations {
            let id = ensure_product_location(
                &left,
                &right,
                &mut locations,
                &mut pair_to_id,
                &mut queue,
                (left_initial, right_initial),
            );
            initial_locations.push(id);
        }
    }
    normalize_ids(&mut initial_locations);

    while let Some((left_state, right_state)) = queue.pop_front() {
        let source = pair_to_id[&(left_state, right_state)];

        for left_transition in &left_outgoing[left_state] {
            let Some(left_label) = left_transition.label.as_ref() else {
                continue;
            };

            for right_transition in &right_outgoing[right_state] {
                let Some(right_label) = right_transition.label.as_ref() else {
                    continue;
                };

                let Some(label) = left_label.intersect(right_label) else {
                    continue;
                };

                let target = ensure_product_location(
                    &left,
                    &right,
                    &mut locations,
                    &mut pair_to_id,
                    &mut queue,
                    (left_transition.target, right_transition.target),
                );

                let mut guards = left_transition.guards.clone();
                guards.extend(
                    right_transition
                        .guards
                        .iter()
                        .map(|guard| shift_clock_constraint(guard, left.num_clocks)),
                );

                let mut resets = left_transition.resets.clone();
                resets.extend(
                    right_transition
                        .resets
                        .iter()
                        .map(|clock| clock + left.num_clocks),
                );
                normalize_ids(&mut resets);

                transitions.push(Transition {
                    source,
                    label: Some(label),
                    guards,
                    resets,
                    target,
                });
            }
        }
    }

    let automaton = TimedAutomaton {
        locations,
        initial_locations,
        num_clocks: left.num_clocks + right.num_clocks,
        transitions,
    };
    debug_assert_well_formed(&automaton);
    automaton
}

/// Concatenate two automata by redirecting accepting transitions of the left
/// operand into the initial locations of the right operand.
fn concatenate<L>(mut left: TimedAutomaton<L>, right: TimedAutomaton<L>) -> TimedAutomaton<L>
where
    L: Clone,
{
    let left_accepting = accepting_location_ids(&left);
    let left_accepts_empty = accepts_empty_word(&left);
    let location_offset = left.locations.len();
    let clock_offset = left.num_clocks;
    let right_initial_locations: Vec<usize> = right
        .initial_locations
        .iter()
        .map(|id| id + location_offset)
        .collect();
    let right_clock_resets = clock_range(clock_offset, right.num_clocks);

    for location in &mut left.locations {
        if left_accepting.contains(&location.id) {
            location.accepting = false;
        }
    }

    let shifted_right_locations: Vec<Location> = right
        .locations
        .into_iter()
        .map(|location| Location {
            id: location.id + location_offset,
            accepting: location.accepting,
        })
        .collect();

    let shifted_right_transitions: Vec<Transition<L>> = right
        .transitions
        .into_iter()
        .map(|transition| shift_transition(&transition, location_offset, clock_offset))
        .collect();

    let redirected_transitions: Vec<Transition<L>> = left
        .transitions
        .iter()
        .filter(|transition| left_accepting.contains(&transition.target))
        .flat_map(|transition| {
            right_initial_locations.iter().copied().map(|target| {
                let mut redirected = transition.clone();
                redirected.target = target;
                redirected.resets.extend(right_clock_resets.iter().copied());
                normalize_ids(&mut redirected.resets);
                redirected
            })
        })
        .collect();

    let mut locations = left.locations;
    locations.extend(shifted_right_locations);

    let mut initial_locations = left.initial_locations;
    if left_accepts_empty {
        initial_locations.extend(right_initial_locations.iter().copied());
        normalize_ids(&mut initial_locations);
    }

    let mut transitions = left.transitions;
    transitions.extend(shifted_right_transitions);
    transitions.extend(redirected_transitions);

    let automaton = TimedAutomaton {
        locations,
        initial_locations,
        num_clocks: left.num_clocks + right.num_clocks,
        transitions,
    };
    debug_assert_well_formed(&automaton);
    automaton
}

/// Extend an automaton so it additionally accepts the empty word.
fn empty_or<L>(mut automaton: TimedAutomaton<L>) -> TimedAutomaton<L> {
    let new_id = automaton.locations.len();
    automaton.locations.push(Location {
        id: new_id,
        accepting: true,
    });
    automaton.initial_locations.push(new_id);
    normalize_ids(&mut automaton.initial_locations);
    debug_assert_well_formed(&automaton);
    automaton
}

/// Add restart transitions implementing one-or-more repetition.
fn plus<L>(automaton: TimedAutomaton<L>) -> TimedAutomaton<L>
where
    L: Clone,
{
    let accepting = accepting_location_ids(&automaton);
    let all_clocks = clock_range(0, automaton.num_clocks);
    let restart_transitions: Vec<Transition<L>> = automaton
        .transitions
        .iter()
        .filter(|transition| accepting.contains(&transition.target))
        .flat_map(|transition| {
            automaton.initial_locations.iter().copied().map(|target| {
                let mut restarted = transition.clone();
                restarted.target = target;
                restarted.resets.extend(all_clocks.iter().copied());
                normalize_ids(&mut restarted.resets);
                restarted
            })
        })
        .collect();

    let mut result = automaton;
    result.transitions.extend(restart_transitions);
    debug_assert_well_formed(&result);
    result
}

/// Build the automaton for zero-or-more repetition.
fn star<L>(automaton: TimedAutomaton<L>) -> TimedAutomaton<L>
where
    L: Clone,
{
    empty_or(plus(automaton))
}

/// Restrict accepted runs to those whose total duration lies in `interval`.
///
/// The construction allocates one fresh clock that measures total elapsed time
/// from the start of the restricted expression.
fn time_restriction<L>(
    mut automaton: TimedAutomaton<L>,
    interval: &Interval,
) -> Result<TimedAutomaton<L>, Error>
where
    L: Clone,
{
    interval.validate()?;

    let accepting = accepting_location_ids(&automaton);
    let accepts_empty = accepts_empty_word(&automaton);
    let total_time_clock = automaton.num_clocks;
    let fresh_accepting_id = automaton.locations.len();

    for location in &mut automaton.locations {
        if accepting.contains(&location.id) {
            location.accepting = false;
        }
    }

    let guard = interval_guard(interval, total_time_clock);
    let redirected: Vec<Transition<L>> = automaton
        .transitions
        .iter()
        .filter(|transition| accepting.contains(&transition.target))
        .map(|transition| {
            let mut redirected = transition.clone();
            redirected.target = fresh_accepting_id;
            redirected.guards.extend(guard.clone());
            redirected
        })
        .collect();

    automaton.locations.push(Location {
        id: fresh_accepting_id,
        accepting: true,
    });
    automaton.num_clocks += 1;
    automaton.transitions.extend(redirected);

    let automaton = if accepts_empty && interval_contains(interval, 0) {
        empty_or(automaton)
    } else {
        automaton
    };

    debug_assert_well_formed(&automaton);
    Ok(automaton)
}

/// Group transitions by source location for efficient product construction.
fn transitions_by_source<L>(automaton: &TimedAutomaton<L>) -> Vec<Vec<&Transition<L>>> {
    let mut outgoing = vec![Vec::new(); automaton.locations.len()];
    for transition in &automaton.transitions {
        outgoing[transition.source].push(transition);
    }
    outgoing
}

/// Return the product location id for `pair`, creating it if needed.
///
/// Newly discovered product states are pushed into `queue` so conjunction can
/// explore them breadth-first.
fn ensure_product_location<L>(
    left: &TimedAutomaton<L>,
    right: &TimedAutomaton<L>,
    locations: &mut Vec<Location>,
    pair_to_id: &mut BTreeMap<(usize, usize), usize>,
    queue: &mut VecDeque<(usize, usize)>,
    pair: (usize, usize),
) -> usize {
    if let Some(&id) = pair_to_id.get(&pair) {
        return id;
    }

    let id = locations.len();
    pair_to_id.insert(pair, id);
    queue.push_back(pair);
    locations.push(Location {
        id,
        accepting: left.locations[pair.0].accepting && right.locations[pair.1].accepting,
    });
    id
}

/// Shift a transition into a larger automaton by offsetting locations and
/// clocks.
fn shift_transition<L>(
    transition: &Transition<L>,
    location_offset: usize,
    clock_offset: usize,
) -> Transition<L>
where
    L: Clone,
{
    Transition {
        source: transition.source + location_offset,
        label: transition.label.clone(),
        guards: transition
            .guards
            .iter()
            .map(|guard| shift_clock_constraint(guard, clock_offset))
            .collect(),
        resets: transition
            .resets
            .iter()
            .map(|clock| clock + clock_offset)
            .collect(),
        target: transition.target + location_offset,
    }
}

/// Shift every clock reference in a guard by `offset`.
fn shift_clock_constraint(constraint: &ClockConstraint, offset: usize) -> ClockConstraint {
    match constraint {
        ClockConstraint::LessThan { clock, bound } => ClockConstraint::LessThan {
            clock: clock + offset,
            bound: *bound,
        },
        ClockConstraint::LessEqual { clock, bound } => ClockConstraint::LessEqual {
            clock: clock + offset,
            bound: *bound,
        },
        ClockConstraint::GreaterThan { clock, bound } => ClockConstraint::GreaterThan {
            clock: clock + offset,
            bound: *bound,
        },
        ClockConstraint::GreaterEqual { clock, bound } => ClockConstraint::GreaterEqual {
            clock: clock + offset,
            bound: *bound,
        },
    }
}

/// Convert a TRE interval into the corresponding conjunction of clock guards.
fn interval_guard(interval: &Interval, clock: usize) -> Vec<ClockConstraint> {
    let mut guards = Vec::new();

    if !(interval.lower_inclusive && interval.lower == 0) {
        guards.push(if interval.lower_inclusive {
            ClockConstraint::GreaterEqual {
                clock,
                bound: interval.lower,
            }
        } else {
            ClockConstraint::GreaterThan {
                clock,
                bound: interval.lower,
            }
        });
    }

    if let Some(upper) = interval.upper {
        guards.push(if interval.upper_inclusive {
            ClockConstraint::LessEqual {
                clock,
                bound: upper,
            }
        } else {
            ClockConstraint::LessThan {
                clock,
                bound: upper,
            }
        });
    }

    guards
}

/// Check whether a concrete duration lies inside `interval`.
fn interval_contains(interval: &Interval, value: u64) -> bool {
    let lower_ok = if interval.lower_inclusive {
        value >= interval.lower
    } else {
        value > interval.lower
    };

    let upper_ok = match interval.upper {
        Some(upper) if interval.upper_inclusive => value <= upper,
        Some(upper) => value < upper,
        None => true,
    };

    lower_ok && upper_ok
}

/// Collect the identifiers of all accepting locations.
fn accepting_location_ids<L>(automaton: &TimedAutomaton<L>) -> Vec<usize> {
    automaton
        .locations
        .iter()
        .filter(|location| location.accepting)
        .map(|location| location.id)
        .collect()
}

/// Check whether an automaton accepts the empty word from one of its initial
/// locations.
fn accepts_empty_word<L>(automaton: &TimedAutomaton<L>) -> bool {
    automaton
        .initial_locations
        .iter()
        .any(|&id| automaton.locations[id].accepting)
}

/// Return the contiguous clock index range `[start, start + count)`.
fn clock_range(start: usize, count: usize) -> Vec<usize> {
    (start..start + count).collect()
}

/// Sort and deduplicate a list of ids in place.
fn normalize_ids(ids: &mut Vec<usize>) {
    ids.sort_unstable();
    ids.dedup();
}

/// Assert the structural invariants expected by the translation helpers.
///
/// This check is debug-only and is used to catch bugs while evolving the
/// construction.
fn debug_assert_well_formed<L>(automaton: &TimedAutomaton<L>) {
    debug_assert!(
        automaton
            .locations
            .iter()
            .enumerate()
            .all(|(index, location)| index == location.id)
    );
    debug_assert!(
        automaton
            .initial_locations
            .iter()
            .all(|&id| id < automaton.locations.len())
    );
    debug_assert!(automaton.transitions.iter().all(|transition| {
        transition.source < automaton.locations.len()
            && transition.target < automaton.locations.len()
            && transition
                .guards
                .iter()
                .all(|guard| constraint_clock(guard) < automaton.num_clocks)
            && transition
                .resets
                .iter()
                .all(|&clock| clock < automaton.num_clocks)
    }));
}

/// Extract the clock index mentioned by a guard.
fn constraint_clock(constraint: &ClockConstraint) -> usize {
    match constraint {
        ClockConstraint::LessThan { clock, .. }
        | ClockConstraint::LessEqual { clock, .. }
        | ClockConstraint::GreaterThan { clock, .. }
        | ClockConstraint::GreaterEqual { clock, .. } => *clock,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, PartialEq, Eq, Hash)]
    struct SymbolSet(Vec<usize>);

    impl SymbolSet {
        fn new(mut values: Vec<usize>) -> Self {
            values.sort_unstable();
            values.dedup();
            Self(values)
        }
    }

    impl LabelIntersect for SymbolSet {
        fn intersect(&self, other: &Self) -> Option<Self> {
            let values = self
                .0
                .iter()
                .copied()
                .filter(|value| other.0.contains(value))
                .collect();
            let intersection = Self::new(values);
            if intersection.0.is_empty() {
                None
            } else {
                Some(intersection)
            }
        }
    }

    #[test]
    fn conjunction_uses_label_intersection_result() {
        let left = atom_automaton(SymbolSet::new(vec![1, 2]));
        let right = atom_automaton(SymbolSet::new(vec![2, 3]));

        let product = conjunction(left, right);

        assert_eq!(product.initial_locations, vec![0]);
        assert_eq!(product.locations.len(), 2);
        assert_eq!(
            product.transitions,
            vec![Transition {
                source: 0,
                label: Some(SymbolSet::new(vec![2])),
                guards: Vec::new(),
                resets: Vec::new(),
                target: 1,
            }]
        );
    }

    #[test]
    fn concatenate_redirects_accepting_transitions_to_right_initials() {
        let concatenated = concatenate(
            atom_automaton("a".to_string()),
            atom_automaton("b".to_string()),
        );

        assert_eq!(concatenated.num_clocks, 0);
        assert_eq!(concatenated.initial_locations, vec![0]);
        assert!(!concatenated.locations[1].accepting);
        assert!(concatenated.locations[3].accepting);
        assert!(concatenated.transitions.iter().any(|transition| {
            transition.source == 0
                && transition.target == 2
                && transition.label == Some("a".to_string())
        }));
    }

    #[test]
    fn time_restriction_preserves_empty_word_only_when_zero_satisfies_interval() {
        let epsilon = epsilon_automaton::<String>();
        let restricted = time_restriction(
            epsilon,
            &Interval {
                lower: 0,
                upper: Some(1),
                lower_inclusive: true,
                upper_inclusive: false,
            },
        )
        .unwrap();

        assert!(accepts_empty_word(&restricted));

        let epsilon = epsilon_automaton::<String>();
        let restricted = time_restriction(
            epsilon,
            &Interval {
                lower: 0,
                upper: Some(1),
                lower_inclusive: false,
                upper_inclusive: false,
            },
        )
        .unwrap();

        assert!(!accepts_empty_word(&restricted));
    }

    #[test]
    fn public_translate_trims_dead_accepting_predecessors() {
        let expr = TimedRegex::Within(
            Box::new(TimedRegex::Concat(
                Box::new(TimedRegex::Atom("a".to_string())),
                Box::new(TimedRegex::Atom("b".to_string())),
            )),
            Interval::left_closed_right_open(1, Some(3)).unwrap(),
        );

        let automaton = translate(&expr).unwrap();

        assert_eq!(automaton.locations.len(), 3);
        assert_eq!(
            automaton.transitions,
            vec![
                Transition {
                    source: 0,
                    label: Some("a".to_string()),
                    guards: Vec::new(),
                    resets: Vec::new(),
                    target: 1,
                },
                Transition {
                    source: 1,
                    label: Some("b".to_string()),
                    guards: vec![
                        ClockConstraint::GreaterEqual { clock: 0, bound: 1 },
                        ClockConstraint::LessThan { clock: 0, bound: 3 },
                    ],
                    resets: Vec::new(),
                    target: 2,
                },
            ]
        );
    }
}
