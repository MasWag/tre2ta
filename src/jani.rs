//! JANI export for timed automata.
//!
//! The current exporter targets a deliberately small subset of JANI v1:
//! a single timed automaton, no constants, no properties, and no network
//! synchronisation.
//!
//! # Examples
//!
//! ```
//! use tre2ta::{parse, to_jani, translate};
//!
//! let expr = parse("(a ; b)%[1, 3)")?;
//! let automaton = translate(&expr)?;
//! let jani = to_jani(&automaton)?;
//!
//! assert!(jani.contains("\"type\": \"ta\""));
//! assert!(jani.contains("\"automata\""));
//! # Ok::<(), tre2ta::Error>(())
//! ```

use std::fmt::Display;

use serde_json::{Map, Value, json};

use crate::{ClockConstraint, Error, Location, TimedAutomaton, Transition};

const MODEL_NAME: &str = "timed_automaton";
const AUTOMATON_NAME: &str = "ta";
const ACCEPTING_VARIABLE: &str = "accepting";
const OP_AND: &str = "\u{2227}";
const OP_LESS_EQUAL: &str = "\u{2264}";

/// Convert a timed automaton into a JANI v1 timed-automata model.
///
/// The exporter validates `automaton` before rendering so malformed location or
/// clock references fail with a structured error instead of producing an
/// inconsistent model.
///
/// # Errors
///
/// Returns [`Error::Export`] when a transition label cannot be represented as a
/// supported JANI action name, when `automaton` is not structurally well
/// formed, or if serializing the JSON model fails. The supported action-name
/// subset is `[A-Za-z_][A-Za-z0-9_]*`.
pub fn to_jani<L: Display>(automaton: &TimedAutomaton<L>) -> Result<String, Error> {
    automaton.validate()?;

    let actions = collect_actions(automaton)?;
    let locations = automaton
        .locations
        .iter()
        .map(location_to_jani)
        .collect::<Vec<_>>();
    let initial_locations = automaton
        .initial_locations
        .iter()
        .copied()
        .map(format_location)
        .map(Value::String)
        .collect::<Vec<_>>();
    let edges = automaton
        .transitions
        .iter()
        .map(transition_to_jani)
        .collect::<Result<Vec<_>, _>>()?;

    let mut model = Map::new();
    model.insert("jani-version".to_owned(), json!(1));
    model.insert("name".to_owned(), json!(MODEL_NAME));
    model.insert("type".to_owned(), json!("ta"));
    if !actions.is_empty() {
        model.insert("actions".to_owned(), Value::Array(actions));
    }
    model.insert(
        "variables".to_owned(),
        Value::Array(vec![json!({
            "name": ACCEPTING_VARIABLE,
            "type": "bool",
            "transient": true,
            "initial-value": false,
        })]),
    );
    model.insert(
        "automata".to_owned(),
        Value::Array(vec![automaton_to_jani(
            automaton.num_clocks,
            locations,
            initial_locations,
            edges,
        )]),
    );
    model.insert(
        "system".to_owned(),
        json!({
            "elements": [
                {
                    "automaton": AUTOMATON_NAME,
                }
            ]
        }),
    );

    serde_json::to_string_pretty(&Value::Object(model))
        .map_err(|error| Error::Export(format!("failed to serialize JANI model: {error}")))
}

fn automaton_to_jani(
    num_clocks: usize,
    locations: Vec<Value>,
    initial_locations: Vec<Value>,
    edges: Vec<Value>,
) -> Value {
    let mut automaton = Map::new();
    automaton.insert("name".to_owned(), json!(AUTOMATON_NAME));

    let variables = (0..num_clocks)
        .map(clock_variable_to_jani)
        .collect::<Vec<_>>();
    if !variables.is_empty() {
        automaton.insert("variables".to_owned(), Value::Array(variables));
    }

    automaton.insert("locations".to_owned(), Value::Array(locations));
    automaton.insert(
        "initial-locations".to_owned(),
        Value::Array(initial_locations),
    );
    automaton.insert("edges".to_owned(), Value::Array(edges));

    Value::Object(automaton)
}

fn clock_variable_to_jani(clock: usize) -> Value {
    json!({
        "name": format_clock(clock),
        "type": "clock",
        "initial-value": 0,
    })
}

fn location_to_jani(location: &Location) -> Value {
    let mut jani_location = Map::new();
    jani_location.insert("name".to_owned(), json!(format_location(location.id)));

    if location.accepting {
        jani_location.insert(
            "transient-values".to_owned(),
            Value::Array(vec![json!({
                "ref": ACCEPTING_VARIABLE,
                "value": true,
            })]),
        );
    }

    Value::Object(jani_location)
}

fn transition_to_jani<L: Display>(transition: &Transition<L>) -> Result<Value, Error> {
    let mut edge = Map::new();
    edge.insert(
        "location".to_owned(),
        json!(format_location(transition.source)),
    );

    if let Some(label) = transition.label.as_ref() {
        edge.insert("action".to_owned(), json!(action_name(label)?));
    }

    if let Some(guard) = guards_to_jani(&transition.guards) {
        edge.insert("guard".to_owned(), json!({ "exp": guard }));
    }

    edge.insert(
        "destinations".to_owned(),
        Value::Array(vec![destination_to_jani(transition)]),
    );

    Ok(Value::Object(edge))
}

fn destination_to_jani<L>(transition: &Transition<L>) -> Value {
    let mut destination = Map::new();
    destination.insert(
        "location".to_owned(),
        json!(format_location(transition.target)),
    );

    let assignments = transition
        .resets
        .iter()
        .copied()
        .map(reset_to_jani)
        .collect::<Vec<_>>();
    if !assignments.is_empty() {
        destination.insert("assignments".to_owned(), Value::Array(assignments));
    }

    Value::Object(destination)
}

fn reset_to_jani(clock: usize) -> Value {
    json!({
        "ref": format_clock(clock),
        "value": 0,
    })
}

fn guards_to_jani(guards: &[ClockConstraint]) -> Option<Value> {
    let mut expressions = guards.iter().map(clock_constraint_to_jani);
    let first = expressions.next()?;

    Some(expressions.fold(first, |left, right| {
        json!({
            "op": OP_AND,
            "left": left,
            "right": right,
        })
    }))
}

fn clock_constraint_to_jani(constraint: &ClockConstraint) -> Value {
    match constraint {
        ClockConstraint::LessThan { clock, bound } => json!({
            "op": "<",
            "left": format_clock(*clock),
            "right": bound,
        }),
        ClockConstraint::LessEqual { clock, bound } => json!({
            "op": OP_LESS_EQUAL,
            "left": format_clock(*clock),
            "right": bound,
        }),
        ClockConstraint::GreaterThan { clock, bound } => json!({
            "op": "<",
            "left": bound,
            "right": format_clock(*clock),
        }),
        ClockConstraint::GreaterEqual { clock, bound } => json!({
            "op": OP_LESS_EQUAL,
            "left": bound,
            "right": format_clock(*clock),
        }),
    }
}

fn collect_actions<L: Display>(automaton: &TimedAutomaton<L>) -> Result<Vec<Value>, Error> {
    let mut names = Vec::<String>::new();

    for transition in &automaton.transitions {
        let Some(label) = transition.label.as_ref() else {
            continue;
        };

        let action = action_name(label)?;
        if !names.contains(&action) {
            names.push(action);
        }
    }

    Ok(names
        .into_iter()
        .map(|name| json!({ "name": name }))
        .collect())
}

fn action_name<L: Display>(label: &L) -> Result<String, Error> {
    let action = label.to_string();

    if !is_valid_action_name(&action) {
        return Err(Error::Export(format!(
            "transition label {action:?} cannot be exported as a JANI action name; supported names match [A-Za-z_][A-Za-z0-9_]*"
        )));
    }

    Ok(action)
}

fn is_valid_action_name(action: &str) -> bool {
    let mut chars = action.chars();
    let Some(first) = chars.next() else {
        return false;
    };

    matches!(first, 'A'..='Z' | 'a'..='z' | '_')
        && chars.all(|ch| matches!(ch, 'A'..='Z' | 'a'..='z' | '0'..='9' | '_'))
}

fn format_location(location: usize) -> String {
    format!("q{location}")
}

fn format_clock(clock: usize) -> String {
    format!("x{clock}")
}
