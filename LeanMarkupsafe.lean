import LeanMarkupsafe.APIs
import LeanMarkupsafe.Proofs.Verified

/-!
# LeanMarkupsafe

A clean-room port of MarkupSafe to Lean 4: an escaped-string type whose invariant is carried in the type, with proved escape/unescape.

Layering, bottom to top (each layer imports only the ones below it):

* `DataTypes/`      structures and inductives; invariants are fields
* `RepoImpl/`       the executable definitions; total, structural recursion
* `Specifications/` the properties, stated in `Prop`
* `Proofs/`         the theorems; `Proofs/Verified.lean` bundles them
* `APIs/`           what users call; returns refinements `{r // Post r}`
-/
