use tre2ta::{
    ClockConstraint, Error, Interval, LabelIntersect, TimedAutomaton, TimedRegex, Transition,
    parse, translate,
};

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

fn assert_well_formed<L>(automaton: &TimedAutomaton<L>) {
    automaton.validate().unwrap();
    assert!(
        automaton
            .transitions
            .iter()
            .all(|transition| transition.label.is_some())
    );
}

fn accepting_transition<'a>(
    automaton: &'a TimedAutomaton<String>,
    label: &str,
) -> &'a Transition<String> {
    automaton
        .transitions
        .iter()
        .find(|transition| {
            transition.label.as_deref() == Some(label)
                && automaton.locations[transition.target].accepting
        })
        .unwrap()
}

fn timed_atom(label: &str, interval: Interval) -> TimedRegex<String> {
    TimedRegex::Within(Box::new(TimedRegex::Atom(label.to_string())), interval)
}

#[test]
fn translates_base_cases() {
    let empty = translate(&parse("empty").unwrap()).unwrap();
    assert_well_formed(&empty);
    assert_eq!(empty.initial_locations, vec![0]);
    assert!(!empty.locations[0].accepting);
    assert!(empty.transitions.is_empty());

    let epsilon = translate(&parse("eps").unwrap()).unwrap();
    assert_well_formed(&epsilon);
    assert_eq!(epsilon.initial_locations, vec![0]);
    assert!(epsilon.locations[0].accepting);
    assert!(epsilon.transitions.is_empty());

    let atom = translate(&parse("a").unwrap()).unwrap();
    assert_well_formed(&atom);
    assert_eq!(
        atom.transitions,
        vec![Transition {
            source: 0,
            label: Some("a".to_string()),
            guards: Vec::new(),
            resets: Vec::new(),
            target: 1,
        }]
    );
}

#[test]
fn translates_union_with_disjoint_union_structure() {
    let automaton = translate(&parse("a | b").unwrap()).unwrap();

    assert_well_formed(&automaton);
    assert_eq!(automaton.locations.len(), 4);
    assert_eq!(automaton.initial_locations, vec![0, 2]);
    assert_eq!(automaton.num_clocks, 0);
    assert_eq!(
        automaton
            .transitions
            .iter()
            .filter_map(|transition| transition.label.clone())
            .collect::<Vec<_>>(),
        vec!["a".to_string(), "b".to_string()]
    );
}

#[test]
fn translates_conjunction_with_string_singleton_labels() {
    let automaton = translate(&parse("a & a").unwrap()).unwrap();

    assert_well_formed(&automaton);
    assert_eq!(automaton.initial_locations, vec![0]);
    assert_eq!(automaton.locations.len(), 2);
    assert_eq!(
        automaton.transitions,
        vec![Transition {
            source: 0,
            label: Some("a".to_string()),
            guards: Vec::new(),
            resets: Vec::new(),
            target: 1,
        }]
    );
}

#[test]
fn translates_conjunction_with_custom_label_intersection() {
    let expr = TimedRegex::Intersection(
        Box::new(TimedRegex::Atom(SymbolSet::new(vec![1, 2]))),
        Box::new(TimedRegex::Atom(SymbolSet::new(vec![2, 3]))),
    );

    let automaton = translate(&expr).unwrap();

    assert_well_formed(&automaton);
    assert_eq!(
        automaton.transitions,
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
fn translates_concatenation_with_redirected_handoff() {
    let automaton = translate(&parse("a ; b").unwrap()).unwrap();

    assert_well_formed(&automaton);
    assert_eq!(automaton.locations.len(), 3);
    assert_eq!(automaton.initial_locations, vec![0]);
    assert!(!automaton.locations[1].accepting);
    assert!(automaton.locations[2].accepting);
    assert!(automaton.transitions.iter().any(|transition| {
        transition.source == 0
            && transition.target == 1
            && transition.label == Some("a".to_string())
    }));
}

#[test]
fn translates_plus_and_star_with_restart_and_empty_word() {
    let plus = translate(&parse("a+").unwrap()).unwrap();
    assert_well_formed(&plus);
    assert!(plus.transitions.iter().any(|transition| {
        transition.source == 0
            && transition.target == 0
            && transition.label == Some("a".to_string())
    }));

    let star = translate(&parse("a*").unwrap()).unwrap();
    assert_well_formed(&star);
    assert!(
        star.initial_locations
            .iter()
            .any(|&id| star.locations[id].accepting)
    );
    assert!(star.transitions.iter().any(|transition| {
        transition.source == 0
            && transition.target == 0
            && transition.label == Some("a".to_string())
    }));
}

#[test]
fn translates_within_by_adding_a_fresh_clock_and_accepting_sink() {
    let automaton = translate(&parse("(a ; b)%[1, 3)").unwrap()).unwrap();

    assert_well_formed(&automaton);
    assert_eq!(automaton.num_clocks, 1);
    assert!(automaton.locations.last().unwrap().accepting);
    assert!(automaton.transitions.iter().any(|transition| {
        transition.label == Some("b".to_string())
            && transition.target == automaton.locations.len() - 1
            && transition.guards
                == vec![
                    ClockConstraint::GreaterEqual { clock: 0, bound: 1 },
                    ClockConstraint::LessThan { clock: 0, bound: 3 },
                ]
    }));
}

#[test]
fn translates_inequality_based_within_guards() {
    let strict_upper = translate(&parse("a%( < 10 )").unwrap()).unwrap();
    assert_well_formed(&strict_upper);
    assert_eq!(
        accepting_transition(&strict_upper, "a").guards,
        vec![ClockConstraint::LessThan {
            clock: 0,
            bound: 10,
        }]
    );

    let inclusive_upper = translate(&parse("a%(<= 10)").unwrap()).unwrap();
    assert_well_formed(&inclusive_upper);
    assert_eq!(
        accepting_transition(&inclusive_upper, "a").guards,
        vec![ClockConstraint::LessEqual {
            clock: 0,
            bound: 10,
        }]
    );

    let strict_lower = translate(&parse("a%( > 3 )").unwrap()).unwrap();
    assert_well_formed(&strict_lower);
    assert_eq!(
        accepting_transition(&strict_lower, "a").guards,
        vec![ClockConstraint::GreaterThan { clock: 0, bound: 3 }]
    );

    let inclusive_lower = translate(&parse("a%(>= 3)").unwrap()).unwrap();
    assert_well_formed(&inclusive_lower);
    assert_eq!(
        accepting_transition(&inclusive_lower, "a").guards,
        vec![ClockConstraint::GreaterEqual { clock: 0, bound: 3 }]
    );
}

#[test]
fn rejects_invalid_intervals_during_translation() {
    let expr = TimedRegex::Within(
        Box::new(TimedRegex::Atom("a".to_string())),
        Interval {
            lower: 3,
            upper: Some(1),
            lower_inclusive: true,
            upper_inclusive: true,
        },
    );

    match translate(&expr).unwrap_err() {
        Error::InvalidInterval { lower, upper } => {
            assert_eq!(lower, 3);
            assert_eq!(upper, 1);
        }
        other => panic!("expected invalid interval error, got {other:?}"),
    }
}

#[test]
fn translates_conjunction_without_matching_labels_as_non_accepting_product() {
    let automaton = translate(&parse("a & b").unwrap()).unwrap();

    assert_well_formed(&automaton);
    assert_eq!(automaton.initial_locations, vec![0]);
    assert_eq!(automaton.locations.len(), 1);
    assert!(!automaton.locations[0].accepting);
    assert!(automaton.transitions.is_empty());
}

#[test]
fn translates_composed_timed_subexpressions_as_well_formed_automata() {
    let concatenated = translate(&TimedRegex::Concat(
        Box::new(timed_atom(
            "a",
            Interval::left_closed_right_open(0, Some(2)).unwrap(),
        )),
        Box::new(timed_atom(
            "b",
            Interval {
                lower: 1,
                upper: None,
                lower_inclusive: true,
                upper_inclusive: false,
            },
        )),
    ))
    .unwrap();
    assert_well_formed(&concatenated);
    assert_eq!(concatenated.num_clocks, 2);

    let plus = translate(&TimedRegex::KleenePlus(Box::new(timed_atom(
        "a",
        Interval::closed(1, Some(3)).unwrap(),
    ))))
    .unwrap();
    assert_well_formed(&plus);
    assert_eq!(plus.num_clocks, 1);

    let star = translate(&TimedRegex::KleeneStar(Box::new(timed_atom(
        "a",
        Interval::left_closed_right_open(0, Some(2)).unwrap(),
    ))))
    .unwrap();
    assert_well_formed(&star);
    assert_eq!(star.num_clocks, 1);
    assert!(
        star.initial_locations
            .iter()
            .any(|&id| star.locations[id].accepting)
    );
}
