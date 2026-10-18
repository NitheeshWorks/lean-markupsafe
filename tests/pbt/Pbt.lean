import LeanMarkupsafe
import Plausible

/-!
# Plausible properties

Each `example` here is a randomised check of a property that is tested
rather than proved, or a restatement of a theorem as a smoke test of the
definitions it is about. They run when this package builds.
-/

namespace Pbt

open LeanMarkupsafe

/-- Smoke test of `unescape_escape`. -/
example : ∀ s : String, unescape (escape s).str = s := by plausible

/-- Smoke test of `escape_length`. -/
example : ∀ s : String, (escape s).str.length = escapedLength s := by plausible

/-- `unescape` is the identity on text without `&` (tested, not proved). -/
example : ∀ s : String, '&' ∈ s.toList ∨ unescape s = s := by plausible

/-- Tag removal never lengthens its input (tested, not proved). -/
example : ∀ l : List Char, (removeTags l).length ≤ l.length := by plausible

/-- Collapsing whitespace never leaves a leading space (tested, not proved). -/
example : ∀ l : List Char, (collapseSpaces l).head? ≠ some ' ' := by plausible

end Pbt
