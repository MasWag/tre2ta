/- TimedAutomata - reusable timed-automata definitions and constructions.

This module provides the core timed-automata infrastructure used by both
TimedRegex (TRE) definitions and the TRE-to-TA correctness proofs.

See `README.md` for usage notes and construction details. -/
import LeanTre2Ta.Basic.Interval
import LeanTre2Ta.Basic.TimedWord
import LeanTre2Ta.TimedAutomata.Syntax
import LeanTre2Ta.TimedAutomata.Semantics
import LeanTre2Ta.TimedAutomata.LabelAlgebra
import LeanTre2Ta.TimedAutomata.Combinators

/- TimedAutomata construction files - they should be imported separately
   to avoid circular dependencies. -/
import LeanTre2Ta.TimedAutomata.Constructions.Concat
import LeanTre2Ta.TimedAutomata.Constructions.Kleene
import LeanTre2Ta.TimedAutomata.Constructions.TimeRestriction
import LeanTre2Ta.TimedAutomata.Constructions.Intersection
