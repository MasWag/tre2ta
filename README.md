# tre2ta

[![License: Apache-2.0 OR MIT](https://img.shields.io/badge/License-Apache--2.0%20OR%20MIT-blue.svg)](#license)
[![Rustdoc](https://img.shields.io/badge/Rustdoc-latest-orange)](https://maswag.github.io/tre2ta/doc)
[![Web Demo](https://img.shields.io/badge/online-available-green)](https://maswag.github.io/tre2ta)

`tre2ta` is a Rust library for translating **timed regular expressions** (TREs) into **timed automata** (TAs).

It provides:

- a TRE AST,
- a TA AST,
- a LALRPOP-based textual parser,
- a translation API,
- a WASM wrapper for browser-facing use,
- Graphviz DOT export,
- and JANI export for a small timed-automata subset.

The crate is meant to be a reusable translation layer rather than a model checker. Property checking is expected to happen in downstream tools. The repository also includes a WASM wrapper used by the browser demo. The note on the construction is available [here](https://maswag.github.io/tre2ta/construction).

## Highlights

- Parsed TREs are semantically validated, so inconsistent intervals are rejected during parsing.
- The public `translate` function validates the TRE and returns a trimmed automaton whose locations can all reach an accepting state.
- The core data structures remain generic in the label type.
- TRE conjunction uses `LabelIntersect` to define label synchronization.

## TRE Syntax

Supported operators:

- union: `|`
- intersection: `&`
- concatenation: `;`
- Kleene star: `*`
- Kleene plus: `+`
- timing constraints via `%`

Examples:

```text
a
a ; b
a | b
a & b
(a ; b)*
(a ; b)+
(a ; b)%[1, 3)
(a | (b ; c))%( < 10 )
(a ; b)%(>= 5)
```

## Example

```rust
use tre2ta::{parse, to_dot, to_jani, translate};

fn main() -> Result<(), tre2ta::Error> {
    let expr = parse("(a ; b)%[1, 3)")?;
    let automaton = translate(&expr)?;
    let dot = to_dot(&automaton)?;
    let jani = to_jani(&automaton)?;
    println!("{dot}");
    println!("{jani}");
    Ok(())
}
```

For custom label domains, use `parse_with`:

```rust
use tre2ta::parse_with;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Label {
    A,
    B,
}

let expr = parse_with("a ; b", |atom| match atom {
    "a" => Ok(Label::A),
    "b" => Ok(Label::B),
    _ => Err("unknown label"),
})?;

assert_eq!(
    expr,
    tre2ta::TimedRegex::Concat(
        Box::new(tre2ta::TimedRegex::Atom(Label::A)),
        Box::new(tre2ta::TimedRegex::Atom(Label::B)),
    )
);
# Ok::<(), tre2ta::Error>(())
```

When constructing values manually, prefer `Interval::new(...)` and `TimedAutomaton::new(...)`. If you build AST nodes or automata directly through public fields, call `validate()` before translation or export.

## Development

Core checks:

```bash
cargo test
```

WASM wrapper:

```bash
cargo test --manifest-path crates/tre2ta-wasm/Cargo.toml
```

For local web demo development, see [web/README.md](web/README.md).

## License

Licensed under either of:

- Apache License, Version 2.0
- MIT license

at your option.
