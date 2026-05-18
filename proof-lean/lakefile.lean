import Lake
open Lake DSL

package «lean-tre2ta» where
  -- The Lean port uses mathlib for real numbers and set notation.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib LeanTre2Ta where
