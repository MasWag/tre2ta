use tre2ta::{ClockConstraint, Error, Location, TimedAutomaton, Transition};

fn assert_well_formed<L>(automaton: &TimedAutomaton<L>) {
    automaton.validate().unwrap();
}

#[test]
fn trim_to_accepting_removes_dead_subgraphs_and_remaps_ids() {
    let automaton = TimedAutomaton {
        locations: vec![
            Location {
                id: 0,
                accepting: false,
            },
            Location {
                id: 1,
                accepting: false,
            },
            Location {
                id: 2,
                accepting: true,
            },
            Location {
                id: 3,
                accepting: false,
            },
            Location {
                id: 4,
                accepting: false,
            },
            Location {
                id: 5,
                accepting: true,
            },
            Location {
                id: 6,
                accepting: false,
            },
            Location {
                id: 7,
                accepting: false,
            },
        ],
        initial_locations: vec![0, 3, 6],
        num_clocks: 2,
        transitions: vec![
            Transition {
                source: 0,
                label: Some("a".to_string()),
                guards: vec![ClockConstraint::LessEqual { clock: 1, bound: 5 }],
                resets: vec![0],
                target: 1,
            },
            Transition {
                source: 1,
                label: None::<String>,
                guards: Vec::new(),
                resets: Vec::new(),
                target: 2,
            },
            Transition {
                source: 3,
                label: Some("dead".to_string()),
                guards: Vec::new(),
                resets: Vec::new(),
                target: 4,
            },
            Transition {
                source: 4,
                label: Some("sink".to_string()),
                guards: Vec::new(),
                resets: Vec::new(),
                target: 4,
            },
            Transition {
                source: 6,
                label: Some("c".to_string()),
                guards: vec![ClockConstraint::GreaterEqual { clock: 0, bound: 2 }],
                resets: vec![1],
                target: 5,
            },
            Transition {
                source: 7,
                label: Some("ghost".to_string()),
                guards: Vec::new(),
                resets: Vec::new(),
                target: 5,
            },
        ],
    };

    let trimmed = automaton.trim_to_accepting().unwrap();

    assert_well_formed(&trimmed);
    assert_eq!(
        trimmed.locations,
        vec![
            Location {
                id: 0,
                accepting: false,
            },
            Location {
                id: 1,
                accepting: false,
            },
            Location {
                id: 2,
                accepting: true,
            },
            Location {
                id: 3,
                accepting: true,
            },
            Location {
                id: 4,
                accepting: false,
            },
            Location {
                id: 5,
                accepting: false,
            },
        ]
    );
    assert_eq!(trimmed.initial_locations, vec![0, 4]);
    assert_eq!(trimmed.num_clocks, 2);
    assert_eq!(
        trimmed.transitions,
        vec![
            Transition {
                source: 0,
                label: Some("a".to_string()),
                guards: vec![ClockConstraint::LessEqual { clock: 1, bound: 5 }],
                resets: vec![0],
                target: 1,
            },
            Transition {
                source: 1,
                label: None,
                guards: Vec::new(),
                resets: Vec::new(),
                target: 2,
            },
            Transition {
                source: 4,
                label: Some("c".to_string()),
                guards: vec![ClockConstraint::GreaterEqual { clock: 0, bound: 2 }],
                resets: vec![1],
                target: 3,
            },
            Transition {
                source: 5,
                label: Some("ghost".to_string()),
                guards: Vec::new(),
                resets: Vec::new(),
                target: 3,
            },
        ]
    );
}

#[test]
fn trim_to_accepting_returns_canonical_empty_language_automaton_when_fully_pruned() {
    let automaton = TimedAutomaton {
        locations: vec![
            Location {
                id: 0,
                accepting: false,
            },
            Location {
                id: 1,
                accepting: false,
            },
            Location {
                id: 2,
                accepting: false,
            },
        ],
        initial_locations: vec![1],
        num_clocks: 3,
        transitions: vec![
            Transition {
                source: 1,
                label: Some("a".to_string()),
                guards: vec![ClockConstraint::LessThan { clock: 2, bound: 7 }],
                resets: vec![0, 2],
                target: 2,
            },
            Transition {
                source: 2,
                label: None::<String>,
                guards: Vec::new(),
                resets: Vec::new(),
                target: 2,
            },
        ],
    };

    let trimmed = automaton.trim_to_accepting().unwrap();

    assert_well_formed(&trimmed);
    assert_eq!(
        trimmed,
        TimedAutomaton {
            locations: vec![Location {
                id: 0,
                accepting: false,
            }],
            initial_locations: vec![0],
            num_clocks: 3,
            transitions: Vec::<Transition<String>>::new(),
        }
    );
}

#[test]
fn validate_rejects_invalid_location_and_clock_references() {
    let automaton = TimedAutomaton {
        locations: vec![Location {
            id: 1,
            accepting: false,
        }],
        initial_locations: vec![0],
        num_clocks: 1,
        transitions: vec![Transition {
            source: 0,
            label: Some("a".to_string()),
            guards: vec![ClockConstraint::LessEqual { clock: 1, bound: 5 }],
            resets: Vec::new(),
            target: 0,
        }],
    };

    match automaton.validate().unwrap_err() {
        Error::InvalidLocationId { index, id } => {
            assert_eq!(index, 0);
            assert_eq!(id, 1);
        }
        other => panic!("expected invalid location id error, got {other:?}"),
    }
}

#[test]
fn checked_constructor_rejects_invalid_initial_locations() {
    let error = TimedAutomaton::<String>::new(
        vec![Location {
            id: 0,
            accepting: false,
        }],
        vec![2],
        0,
        Vec::new(),
    )
    .unwrap_err();

    match error {
        Error::InvalidInitialLocation {
            location,
            num_locations,
        } => {
            assert_eq!(location, 2);
            assert_eq!(num_locations, 1);
        }
        other => panic!("expected invalid initial location error, got {other:?}"),
    }
}
