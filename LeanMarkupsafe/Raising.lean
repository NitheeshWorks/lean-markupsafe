import LeanMarkupsafe

/-!
# Raising variants (opt-in)

Not part of the core API, and not imported by `import LeanMarkupsafe`:
`import LeanMarkupsafe.Raising` to use it. Upstream raises where the core API
returns `Except FormatError Markup`. Where a caller must produce `Markup`
and a failure can only be a programming error (a literal template in a
`HasHtml` instance, as in the docs' `User.__html__`), `format!` panics
instead, like Lean's `get!`. Nothing in the verified library calls it.
-/

namespace LeanMarkupsafe

/-- `format`, panicking where upstream would raise. -/
def Markup.format! {α : Type u} [ToPercentArgs α] (t : Markup) (args : α) : Markup :=
  match t.format args with
  | .ok m => m
  | .error e => panic! (toString e)

end LeanMarkupsafe
