use tre2ta::{ClockConstraint, Location, TimedAutomaton, Transition, parse, to_dot, translate};

#[test]
fn exports_atom_automaton_as_stable_dot() {
    let automaton = translate(&parse("a").unwrap()).unwrap();

    assert_eq!(
        to_dot(&automaton).unwrap(),
        concat!(
            "digraph timed_automaton {\n",
            "    q0 [label=\"q0\", shape=circle];\n",
            "    q1 [label=\"q1\", shape=doublecircle];\n",
            "    init_0 [label=\"\", shape=point];\n",
            "    init_0 -> q0;\n",
            "    q0 -> q1 [label=\"a\"];\n",
            "}\n",
        )
    );
}

#[test]
fn exports_multiple_initial_locations_and_accepting_nodes() {
    let automaton = translate(&parse("eps | a").unwrap()).unwrap();
    let dot = to_dot(&automaton).unwrap();

    assert!(dot.contains("q0 [label=\"q0\", shape=doublecircle];"));
    assert!(dot.contains("q2 [label=\"q2\", shape=doublecircle];"));
    assert!(dot.contains("init_0 -> q0;"));
    assert!(dot.contains("init_1 -> q1;"));
}

#[test]
fn exports_guarded_transitions_from_translation() {
    let automaton = translate(&parse("(a ; b)%[1, 3)").unwrap()).unwrap();
    let dot = to_dot(&automaton).unwrap();

    assert!(dot.contains("label=\"b\\nguard: x0 >= 1 && x0 < 3\""));
}

#[test]
fn omits_trivial_lower_bound_from_upper_bound_only_translation() {
    let automaton = translate(&parse("a%( < 10 )").unwrap()).unwrap();
    let dot = to_dot(&automaton).unwrap();

    assert!(dot.contains("label=\"a\\nguard: x0 < 10\""));
    assert!(!dot.contains("x0 >= 0"));
}

#[test]
fn exports_reset_transitions_from_translation() {
    let automaton = translate(&parse("((a)%[1, 3))+").unwrap()).unwrap();
    let dot = to_dot(&automaton).unwrap();

    assert!(dot.contains("q0 -> q0 [label=\"a\\nguard: x0 >= 1 && x0 < 3\\nreset: x0\"]"));
}

#[test]
fn renders_none_labels_as_eps() {
    let automaton = TimedAutomaton {
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
            label: None::<String>,
            guards: Vec::new(),
            resets: Vec::new(),
            target: 1,
        }],
    };

    assert!(
        to_dot(&automaton)
            .unwrap()
            .contains("q0 -> q1 [label=\"eps\"]")
    );
}

#[test]
fn escapes_special_characters_in_dot_labels() {
    let automaton = TimedAutomaton {
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
        num_clocks: 1,
        transitions: vec![Transition {
            source: 0,
            label: Some("a\"b\\c\nd".to_string()),
            guards: vec![ClockConstraint::LessEqual { clock: 0, bound: 2 }],
            resets: vec![0],
            target: 1,
        }],
    };

    assert!(
        to_dot(&automaton)
            .unwrap()
            .contains("q0 -> q1 [label=\"a\\\"b\\\\c\\nd\\nguard: x0 <= 2\\nreset: x0\"]")
    );
}

#[test]
fn rejects_invalid_automata() {
    let automaton = TimedAutomaton {
        locations: Vec::<Location>::new(),
        initial_locations: Vec::new(),
        num_clocks: 0,
        transitions: Vec::<Transition<String>>::new(),
    };

    match to_dot(&automaton).unwrap_err() {
        tre2ta::Error::EmptyAutomaton => {}
        other => panic!("expected invalid automaton error, got {other:?}"),
    }
}
