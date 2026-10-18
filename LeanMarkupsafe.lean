import LeanMarkupsafe.APIs
import LeanMarkupsafe.Proofs.Verified

/-!
# LeanMarkupsafe

A clean-room port of MarkupSafe to Lean 4, with proved escape/unescape.
`Markup` is trusted, unchecked HTML (upstream semantics); the proved
invariant is carried by `Escaped := {m : Markup // IsEscaped m.str}`, by the
`API.*` refinements, and by the provenance theorems for trusted templates.

Layering, bottom to top (each layer imports only the ones below it):

* `DataTypes/`      structures and inductives; invariants are fields
* `RepoImpl/`       the executable definitions; total, structural recursion
* `Specifications/` the properties, stated in `Prop`
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
* `APIs/`           what users call; returns refinements `{r // Post r}`
-/
