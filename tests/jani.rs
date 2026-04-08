use serde_json::{Value, json};
use tre2ta::{
    ClockConstraint, Error, Location, TimedAutomaton, Transition, parse, to_jani, translate,
};

const OP_AND: &str = "\u{2227}";
const OP_LESS_EQUAL: &str = "\u{2264}";

fn export_value<L: std::fmt::Display>(automaton: &TimedAutomaton<L>) -> Value {
    serde_json::from_str(&to_jani(automaton).unwrap()).unwrap()
}

fn exported_automaton(model: &Value) -> &Value {
    &model["automata"][0]
}

fn location_named<'a>(automaton: &'a Value, name: &str) -> &'a Value {
    automaton["locations"]
        .as_array()
        .unwrap()
        .iter()
        .find(|location| location["name"] == name)
        .unwrap()
}

#[test]
fn exports_atom_automaton_as_single_ta_model() {
    let model = export_value(&translate(&parse("a").unwrap()).unwrap());
    let automaton = exported_automaton(&model);

    assert_eq!(model["jani-version"], json!(1));
    assert_eq!(model["name"], json!("timed_automaton"));
    assert_eq!(model["type"], json!("ta"));
    assert_eq!(model["actions"], json!([{ "name": "a" }]));
    assert_eq!(automaton["name"], json!("ta"));
    assert_eq!(automaton["initial-locations"], json!(["q0"]));
    assert_eq!(
        automaton["edges"],
        json!([
            {
                "action": "a",
                "location": "q0",
                "destinations": [
                    {
                        "location": "q1"
                    }
                ]
            }
        ])
    );
    assert_eq!(
        model["system"],
        json!({
            "elements": [
                {
                    "automaton": "ta"
                }
            ]
        })
    );
}

#[test]
fn exports_guards_with_base_jani_comparisons() {
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
        num_clocks: 4,
        transitions: vec![Transition {
            source: 0,
            label: Some("a".to_string()),
            guards: vec![
                ClockConstraint::LessThan { clock: 0, bound: 5 },
                ClockConstraint::LessEqual { clock: 1, bound: 6 },
                ClockConstraint::GreaterThan { clock: 2, bound: 7 },
                ClockConstraint::GreaterEqual { clock: 3, bound: 8 },
            ],
            resets: Vec::new(),
            target: 1,
        }],
    };

    let model = export_value(&automaton);
    let jani_automaton = exported_automaton(&model);

    assert_eq!(
        jani_automaton["variables"],
        json!([
            { "name": "x0", "type": "clock", "initial-value": 0 },
            { "name": "x1", "type": "clock", "initial-value": 0 },
            { "name": "x2", "type": "clock", "initial-value": 0 },
            { "name": "x3", "type": "clock", "initial-value": 0 }
        ])
    );
    assert_eq!(
        jani_automaton["edges"][0]["guard"]["exp"],
        json!({
            "op": OP_AND,
            "left": {
                "op": OP_AND,
                "left": {
                    "op": OP_AND,
                    "left": { "op": "<", "left": "x0", "right": 5 },
                    "right": { "op": OP_LESS_EQUAL, "left": "x1", "right": 6 }
                },
                "right": { "op": "<", "left": 7, "right": "x2" }
            },
            "right": { "op": OP_LESS_EQUAL, "left": 8, "right": "x3" }
        })
    );
}

#[test]
fn exports_resets_as_clock_assignments_to_zero() {
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
        num_clocks: 3,
        transitions: vec![Transition {
            source: 0,
            label: Some("a".to_string()),
            guards: Vec::new(),
            resets: vec![0, 2],
            target: 1,
        }],
    };

    let model = export_value(&automaton);
    let assignments = &exported_automaton(&model)["edges"][0]["destinations"][0]["assignments"];

    assert_eq!(
        assignments,
        &json!([
            { "ref": "x0", "value": 0 },
            { "ref": "x2", "value": 0 }
        ])
    );
}

#[test]
fn exports_multiple_initial_locations() {
    let model = export_value(&translate(&parse("eps | a").unwrap()).unwrap());

    assert_eq!(
        exported_automaton(&model)["initial-locations"],
        json!(["q0", "q1"])
    );
}

#[test]
fn omits_trivial_lower_bound_from_upper_bound_only_translation() {
    let model = export_value(&translate(&parse("a%(<= 10)").unwrap()).unwrap());
    let edge = exported_automaton(&model)["edges"]
        .as_array()
        .unwrap()
        .iter()
        .find(|edge| edge.get("guard").is_some())
        .unwrap();

    assert_eq!(
        edge["guard"]["exp"],
        json!({
            "op": OP_LESS_EQUAL,
            "left": "x0",
            "right": 10
        })
    );
}

#[test]
fn omits_action_for_silent_transitions() {
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

    let model = export_value(&automaton);
    let edge = exported_automaton(&model)["edges"][0].as_object().unwrap();

    assert!(!edge.contains_key("action"));
}

#[test]
fn exports_accepting_locations_via_transient_variable() {
    let model = export_value(&translate(&parse("a").unwrap()).unwrap());
    let automaton = exported_automaton(&model);

    assert_eq!(
        model["variables"],
        json!([
            {
                "name": "accepting",
                "type": "bool",
                "transient": true,
                "initial-value": false
            }
        ])
    );
    assert!(
        location_named(automaton, "q0")
            .as_object()
            .unwrap()
            .get("transient-values")
            .is_none()
    );
    assert_eq!(
        location_named(automaton, "q1")["transient-values"],
        json!([
            {
                "ref": "accepting",
                "value": true
            }
        ])
    );
}

#[test]
fn deduplicates_actions_in_first_seen_order() {
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
        ],
        initial_locations: vec![0],
        num_clocks: 0,
        transitions: vec![
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
                guards: Vec::new(),
                resets: Vec::new(),
                target: 2,
            },
            Transition {
                source: 0,
                label: Some("a".to_string()),
                guards: Vec::new(),
                resets: Vec::new(),
                target: 2,
            },
        ],
    };

    let model = export_value(&automaton);

    assert_eq!(model["actions"], json!([{ "name": "a" }, { "name": "b" }]));
}

#[test]
fn rejects_invalid_action_labels() {
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
            label: Some(String::new()),
            guards: Vec::new(),
            resets: Vec::new(),
            target: 1,
        }],
    };

    match to_jani(&automaton).unwrap_err() {
        Error::Export(message) => {
            assert!(message.contains("[A-Za-z_][A-Za-z0-9_]*"));
        }
        other => panic!("expected export error, got {other:?}"),
    }
}

#[test]
fn rejects_action_labels_outside_supported_identifier_subset() {
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
            label: Some("not-valid".to_string()),
            guards: Vec::new(),
            resets: Vec::new(),
            target: 1,
        }],
    };

    match to_jani(&automaton).unwrap_err() {
        Error::Export(message) => {
            assert!(message.contains("not-valid"));
            assert!(message.contains("[A-Za-z_][A-Za-z0-9_]*"));
        }
        other => panic!("expected export error, got {other:?}"),
    }
}

#[test]
fn rejects_invalid_automata_before_export() {
    let automaton = TimedAutomaton {
        locations: vec![Location {
            id: 0,
            accepting: false,
        }],
        initial_locations: vec![1],
        num_clocks: 0,
        transitions: Vec::<Transition<String>>::new(),
    };

    match to_jani(&automaton).unwrap_err() {
        Error::InvalidInitialLocation {
            location,
            num_locations,
        } => {
            assert_eq!(location, 1);
            assert_eq!(num_locations, 1);
        }
        other => panic!("expected invalid automaton error, got {other:?}"),
    }
}
