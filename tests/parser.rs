use tre2ta::{Error, Interval, TimedRegex, parse, parse_with};

fn atom(label: &str) -> TimedRegex<String> {
    TimedRegex::Atom(label.to_string())
}

fn union(left: TimedRegex<String>, right: TimedRegex<String>) -> TimedRegex<String> {
    TimedRegex::Union(Box::new(left), Box::new(right))
}

fn intersection(left: TimedRegex<String>, right: TimedRegex<String>) -> TimedRegex<String> {
    TimedRegex::Intersection(Box::new(left), Box::new(right))
}

fn concat(left: TimedRegex<String>, right: TimedRegex<String>) -> TimedRegex<String> {
    TimedRegex::Concat(Box::new(left), Box::new(right))
}

fn star(expr: TimedRegex<String>) -> TimedRegex<String> {
    TimedRegex::KleeneStar(Box::new(expr))
}

fn plus(expr: TimedRegex<String>) -> TimedRegex<String> {
    TimedRegex::KleenePlus(Box::new(expr))
}

fn within(expr: TimedRegex<String>, interval: Interval) -> TimedRegex<String> {
    TimedRegex::Within(Box::new(expr), interval)
}

fn interval(
    lower: u64,
    upper: Option<u64>,
    lower_inclusive: bool,
    upper_inclusive: bool,
) -> Interval {
    Interval {
        lower,
        upper,
        lower_inclusive,
        upper_inclusive,
    }
}

fn assert_parse_error(input: &str) {
    match parse(input) {
        Err(Error::Parse(message)) => assert!(!message.is_empty()),
        other => panic!("expected parse error for {input:?}, got {other:?}"),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TestLabel {
    A,
    B,
    C,
}

fn label_atom(label: TestLabel) -> TimedRegex<TestLabel> {
    TimedRegex::Atom(label)
}

fn parse_test_label(input: &str) -> Result<TestLabel, &'static str> {
    match input {
        "a" => Ok(TestLabel::A),
        "b" => Ok(TestLabel::B),
        "c" => Ok(TestLabel::C),
        _ => Err("unknown label"),
    }
}

#[test]
fn parses_literals_and_base_forms() {
    assert_eq!(parse("a").unwrap(), atom("a"));
    assert_eq!(parse("eps").unwrap(), TimedRegex::Epsilon);
    assert_eq!(parse("empty").unwrap(), TimedRegex::Empty);
    assert_eq!(parse("_foo1").unwrap(), atom("_foo1"));
}

#[test]
fn parses_operator_precedence() {
    assert_eq!(
        parse("a | b & c").unwrap(),
        union(atom("a"), intersection(atom("b"), atom("c")))
    );
    assert_eq!(
        parse("a & b ; c").unwrap(),
        intersection(atom("a"), concat(atom("b"), atom("c")))
    );
}

#[test]
fn parses_left_associative_binary_operators() {
    assert_eq!(
        parse("a ; b ; c").unwrap(),
        concat(concat(atom("a"), atom("b")), atom("c"))
    );
    assert_eq!(
        parse("a | b | c").unwrap(),
        union(union(atom("a"), atom("b")), atom("c"))
    );
}

#[test]
fn parses_postfix_operators_and_binding() {
    assert_eq!(parse("a*").unwrap(), star(atom("a")));
    assert_eq!(parse("a+").unwrap(), plus(atom("a")));
    assert_eq!(
        parse("(a ; b)*").unwrap(),
        star(concat(atom("a"), atom("b")))
    );
    assert_eq!(
        parse("(a ; b)+").unwrap(),
        plus(concat(atom("a"), atom("b")))
    );
    assert_eq!(parse("a*+").unwrap(), plus(star(atom("a"))));
    assert_eq!(
        parse("(a ; b)%[1, 3)").unwrap(),
        within(
            concat(atom("a"), atom("b")),
            interval(1, Some(3), true, false)
        )
    );
}

#[test]
fn parses_timing_constraint_variants() {
    assert_eq!(
        parse("a%[1, 3)").unwrap(),
        within(atom("a"), interval(1, Some(3), true, false))
    );
    assert_eq!(
        parse("a%(1, 3]").unwrap(),
        within(atom("a"), interval(1, Some(3), false, true))
    );
    assert_eq!(
        parse("a%[1, inf)").unwrap(),
        within(atom("a"), interval(1, None, true, false))
    );
    assert_eq!(
        parse("a%( < 10 )").unwrap(),
        within(atom("a"), interval(0, Some(10), true, false))
    );
    assert_eq!(
        parse("a%(<= 10)").unwrap(),
        within(atom("a"), interval(0, Some(10), true, true))
    );
    assert_eq!(
        parse("a%( > 3 )").unwrap(),
        within(atom("a"), interval(3, None, false, false))
    );
    assert_eq!(
        parse("a%(>= 3)").unwrap(),
        within(atom("a"), interval(3, None, true, false))
    );
}

#[test]
fn parses_nested_documented_example() {
    assert_eq!(
        parse("(a | (b ; c))%( < 10 )").unwrap(),
        within(
            union(atom("a"), concat(atom("b"), atom("c"))),
            interval(0, Some(10), true, false),
        )
    );
}

#[test]
fn rejects_malformed_inputs() {
    for input in ["a |", "%", "a%", "(a ; b", "a%[1 x 3)", "1a"] {
        assert_parse_error(input);
    }
}

#[test]
fn rejects_invalid_intervals_during_parsing() {
    match parse("a%[3, 1]").unwrap_err() {
        Error::InvalidInterval { lower, upper } => {
            assert_eq!(lower, 3);
            assert_eq!(upper, 1);
        }
        other => panic!("expected invalid interval error, got {other:?}"),
    }
}

#[test]
fn parse_with_supports_custom_labels() {
    assert_eq!(
        parse_with("a & b", parse_test_label).unwrap(),
        TimedRegex::Intersection(
            Box::new(label_atom(TestLabel::A)),
            Box::new(label_atom(TestLabel::B))
        )
    );
}

#[test]
fn parse_with_preserves_precedence_postfix_and_timing() {
    assert_eq!(
        parse_with("(a | (b ; c))%( < 10 )", parse_test_label).unwrap(),
        TimedRegex::Within(
            Box::new(TimedRegex::Union(
                Box::new(label_atom(TestLabel::A)),
                Box::new(TimedRegex::Concat(
                    Box::new(label_atom(TestLabel::B)),
                    Box::new(label_atom(TestLabel::C))
                ))
            )),
            interval(0, Some(10), true, false),
        )
    );
}

#[test]
fn parse_with_maps_label_parser_failures_into_parse_errors() {
    match parse_with("d", parse_test_label) {
        Err(Error::Parse(message)) => {
            assert!(message.contains("invalid atom \"d\""));
            assert!(message.contains("unknown label"));
        }
        other => panic!("expected parse error, got {other:?}"),
    }
}

#[test]
fn parse_with_reports_syntax_errors() {
    match parse_with::<TestLabel, _, _>("a |", parse_test_label) {
        Err(Error::Parse(message)) => assert!(message.contains("Unrecognized EOF")),
        other => panic!("expected parse error, got {other:?}"),
    }
}
