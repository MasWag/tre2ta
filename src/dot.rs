//! Graphviz DOT export for timed automata.

use std::fmt::{Display, Write};

use crate::{ClockConstraint, Error, TimedAutomaton, Transition};

/// Convert a timed automaton into Graphviz DOT.
///
/// The exporter validates `automaton` before rendering so malformed location or
/// clock references fail with a structured error instead of producing invalid
/// DOT.
///
/// # Examples
///
/// ```
/// use tre2ta::{parse, to_dot, translate};
///
/// let expr = parse("(a ; b)%[1, 3)")?;
/// let automaton = translate(&expr)?;
/// let dot = to_dot(&automaton)?;
///
/// assert!(dot.starts_with("digraph timed_automaton {"));
/// assert!(dot.contains("guard: x0 >= 1 && x0 < 3"));
/// # Ok::<(), tre2ta::Error>(())
/// ```
///
/// # Errors
///
/// Returns an error when `automaton` is not structurally well formed.
pub fn to_dot<L: Display>(automaton: &TimedAutomaton<L>) -> Result<String, Error> {
    automaton.validate()?;

    let mut dot = String::new();
    writeln!(&mut dot, "digraph timed_automaton {{").expect("writing to String cannot fail");

    for location in &automaton.locations {
        let shape = if location.accepting {
            "doublecircle"
        } else {
            "circle"
        };
        writeln!(
            &mut dot,
            "    q{} [label=\"q{}\", shape={}];",
            location.id, location.id, shape
        )
        .expect("writing to String cannot fail");
    }

    for (index, initial) in automaton.initial_locations.iter().enumerate() {
        writeln!(&mut dot, "    init_{index} [label=\"\", shape=point];")
            .expect("writing to String cannot fail");
        writeln!(&mut dot, "    init_{index} -> q{initial};")
            .expect("writing to String cannot fail");
    }

    for transition in &automaton.transitions {
        writeln!(
            &mut dot,
            "    q{} -> q{} [label=\"{}\"];",
            transition.source,
            transition.target,
            escape_dot(&format_transition_label(transition))
        )
        .expect("writing to String cannot fail");
    }

    writeln!(&mut dot, "}}").expect("writing to String cannot fail");
    Ok(dot)
}

fn format_transition_label<L: Display>(transition: &Transition<L>) -> String {
    let mut lines = vec![match &transition.label {
        Some(label) => label.to_string(),
        None => "eps".to_string(),
    }];

    if !transition.guards.is_empty() {
        lines.push(format!("guard: {}", format_guards(&transition.guards)));
    }

    if !transition.resets.is_empty() {
        lines.push(format!("reset: {}", format_resets(&transition.resets)));
    }

    lines.join("\n")
}

/// Format a conjunction of guards for DOT edge labels.
fn format_guards(guards: &[ClockConstraint]) -> String {
    guards
        .iter()
        .map(format_guard)
        .collect::<Vec<_>>()
        .join(" && ")
}

/// Format a single clock guard using the crate's `x{n}` clock naming scheme.
fn format_guard(guard: &ClockConstraint) -> String {
    match guard {
        ClockConstraint::LessThan { clock, bound } => {
            format!("{} < {}", format_clock(*clock), bound)
        }
        ClockConstraint::LessEqual { clock, bound } => {
            format!("{} <= {}", format_clock(*clock), bound)
        }
        ClockConstraint::GreaterThan { clock, bound } => {
            format!("{} > {}", format_clock(*clock), bound)
        }
        ClockConstraint::GreaterEqual { clock, bound } => {
            format!("{} >= {}", format_clock(*clock), bound)
        }
    }
}

/// Format a list of clock resets for DOT output.
fn format_resets(resets: &[usize]) -> String {
    resets
        .iter()
        .map(|clock| format_clock(*clock))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Format a clock index using the exported textual name used in DOT output.
fn format_clock(clock: usize) -> String {
    format!("x{clock}")
}

/// Escape a label so it is safe to embed in a DOT string literal.
fn escape_dot(input: &str) -> String {
    let mut escaped = String::with_capacity(input.len());
    for ch in input.chars() {
        match ch {
            '\\' => escaped.push_str("\\\\"),
            '"' => escaped.push_str("\\\""),
            '\n' => escaped.push_str("\\n"),
            _ => escaped.push(ch),
        }
    }
    escaped
}
