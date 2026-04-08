#!/bin/sh
set -eu

if command -v rustup >/dev/null 2>&1; then
  if rustup toolchain list 2>/dev/null | grep -q '^stable'; then
    toolchain_bin=$(dirname "$(rustup which rustc --toolchain stable)")
    PATH="$toolchain_bin:$PATH"
    export PATH
  fi
fi

wasm-pack build ../crates/tre2ta-wasm --target web --out-dir ../../web/pkg
