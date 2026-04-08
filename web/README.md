# tre2ta web demo

This directory contains the small static browser demo for `tre2ta`.

## Prerequisites

- a Rust toolchain with the `wasm32-unknown-unknown` target installed
- [`wasm-pack`](https://rustwasm.github.io/wasm-pack/installer/)
- Node.js and npm

## Commands

```bash
npm install
npm run dev
```

Useful extras:

```bash
npm run wasm
npm run build
npm test
```

The `wasm` script builds the bindings from `../crates/tre2ta-wasm` into `web/pkg`.
If Rustup with a `stable` toolchain is available, the script prefers that toolchain automatically.
Otherwise it uses the current `PATH`, so make sure that toolchain already has the `wasm32-unknown-unknown` target available.
