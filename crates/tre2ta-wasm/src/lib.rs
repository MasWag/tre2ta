use wasm_bindgen::prelude::*;

fn translate_trimmed(input: &str) -> Result<tre2ta::TimedAutomaton<String>, String> {
    let expression = tre2ta::parse(input).map_err(|error| error.to_string())?;
    tre2ta::translate(&expression).map_err(|error| error.to_string())
}

fn tre_to_dot_impl(input: &str) -> Result<String, String> {
    let automaton = translate_trimmed(input)?;
    tre2ta::to_dot(&automaton).map_err(|error| error.to_string())
}

fn tre_to_jani_impl(input: &str) -> Result<String, String> {
    let automaton = translate_trimmed(input)?;
    tre2ta::to_jani(&automaton).map_err(|error| error.to_string())
}

/// Translate a textual timed regular expression into Graphviz DOT.
///
/// # Errors
///
/// Returns a JavaScript `Error` when parsing or translation fails.
#[wasm_bindgen(js_name = treToDot)]
pub fn tre_to_dot(input: &str) -> Result<String, JsError> {
    tre_to_dot_impl(input).map_err(|message| JsError::new(&message))
}

/// Translate a textual timed regular expression into JANI.
///
/// # Errors
///
/// Returns a JavaScript `Error` when parsing, translation, or JANI export fails.
#[wasm_bindgen(js_name = treToJani)]
pub fn tre_to_jani(input: &str) -> Result<String, JsError> {
    tre_to_jani_impl(input).map_err(|message| JsError::new(&message))
}

#[cfg(test)]
mod tests {
    use super::{tre_to_dot_impl, tre_to_jani_impl};

    #[test]
    fn returns_dot_for_a_valid_tre() {
        let dot = tre_to_dot_impl("(a ; b)%[1, 3)").expect("valid TRE should translate");

        assert!(dot.starts_with("digraph timed_automaton {"));
        assert!(dot.contains("guard: x0 >= 1 && x0 < 3"));
    }

    #[test]
    fn surfaces_parse_errors() {
        let error = tre_to_dot_impl("a ;").expect_err("invalid TRE should fail");

        assert!(error.starts_with("parse error:"));
    }

    #[test]
    fn surfaces_invalid_interval_errors() {
        let error = tre_to_dot_impl("a%[3, 1]").expect_err("invalid interval should fail");

        assert_eq!(
            error,
            "invalid interval: lower bound 3 exceeds upper bound 1"
        );
    }

    #[test]
    fn returns_jani_for_a_valid_tre() {
        let jani = tre_to_jani_impl("(a ; b)%[1, 3)").expect("valid TRE should translate");

        assert!(jani.contains("\"jani-version\""));
        assert!(jani.contains("\"automata\""));
    }

    #[test]
    fn omits_trivial_lower_bound_from_dot_export() {
        let dot = tre_to_dot_impl("a%( < 10 )").expect("valid TRE should translate");

        assert!(dot.contains("guard: x0 < 10"));
        assert!(!dot.contains("x0 >= 0"));
    }

    #[test]
    fn omits_trivial_lower_bound_from_jani_export() {
        let jani = tre_to_jani_impl("a%(<= 10)").expect("valid TRE should translate");

        assert!(jani.contains("\"left\": \"x0\""));
        assert!(jani.contains("\"right\": 10"));
        assert!(!jani.contains("\"right\": \"x0\""));
    }

    #[test]
    fn trims_dead_locations_before_dot_export() {
        let dot = tre_to_dot_impl("(a ; b)%[1, 3)").expect("valid TRE should translate");

        assert!(dot.contains("q0 [label=\"q0\", shape=circle];"));
        assert!(dot.contains("q1 [label=\"q1\", shape=circle];"));
        assert!(dot.contains("q2 [label=\"q2\", shape=doublecircle];"));
        assert!(!dot.contains("q3 [label=\"q3\""));
        assert!(!dot.contains("q2 -> q3 [label=\"b\"]"));
    }

    #[test]
    fn trims_dead_locations_before_jani_export() {
        let jani = tre_to_jani_impl("(a ; b)%[1, 3)").expect("valid TRE should translate");

        assert!(jani.contains("\"locations\""));
        assert!(jani.contains("\"name\": \"q0\""));
        assert!(jani.contains("\"name\": \"q1\""));
        assert!(jani.contains("\"name\": \"q2\""));
        assert!(!jani.contains("\"name\": \"q3\""));
    }
}
