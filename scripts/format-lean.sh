#!/usr/bin/env bash
set -euo pipefail

if ! command -v lean-fmt >/dev/null 2>&1; then
  echo "error: lean-fmt is not installed." >&2
  echo "Install it with:" >&2
  echo "  go install github.com/lotusirous/lean-fmt@v0.3.4" >&2
  exit 1
fi

for file in "$@"; do
  [ -f "$file" ] || continue

  tmp="$(mktemp)"
  lean-fmt "$file" > "$tmp"

  if ! cmp -s "$file" "$tmp"; then
    mv "$tmp" "$file"
  else
    rm "$tmp"
  fi
done

