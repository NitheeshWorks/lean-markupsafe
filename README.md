# lean-markupsafe

[![Lean 4](https://img.shields.io/badge/built%20with-Lean%204-blue.svg)](https://lean-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-machine%20checked-brightgreen.svg)](CONTRIBUTING.md#verification)

A clean-room port of [MarkupSafe](https://github.com/pallets/markupsafe) to Lean 4: an escaped-string type whose invariant is carried in the type, with proved escape/unescape.

Part of the verified FastAPI stack: [lean-fastapi](https://github.com/NitheeshWorks/lean-fastapi)
and its dependencies, each ported as its own repo with its proofs. This one
depends on: none (Lean core only).

## What "verified" means here

* Public functions take the weakest precondition they need and return the
  strongest postcondition, as a refinement type `{r // Post r}` or an
  `Except` of one. Invariants live in types, not comments.
* Every theorem is machine-checked. CI fails on `sorry` and on any axiom
  beyond Lean's own `propext`, `Quot.sound` and `Classical.choice`.
* What is tested rather than proved is listed, with the reason, in
  [CONTRIBUTING.md](CONTRIBUTING.md#verification) and in
  `docs/traceability.toml`.

## Getting started

```
lake build            # library, proofs, and both test executables
lake exe props        # property tests (seeded; `lake exe props 42`)
lake exe conformance  # cases re-expressed from the upstream test suite
scripts/check.sh      # the whole CI gate, locally
```

Toolchain: `leanprover/lean4:v4.35.0` (pinned in `lean-toolchain`; `elan` installs it).

## Using it

```lean
import LeanMarkupsafe
open LeanMarkupsafe

#eval (escape "<b>&</b>").str                     -- "&lt;b&gt;&amp;&lt;/b&gt;"
#eval (Markup.mk "<em>" ++ "<x>" ++ Markup.mk "</em>").str   -- "<em>&lt;x&gt;</em>"
#eval (Markup.mk "<p>{}</p>").format [.ofString "a < b"]     -- ok "<p>a &lt; b</p>"
#eval (Markup.mk "Main &raquo;\t<em>About</em>").striptags  -- "Main » About"
```

A type opts into safe rendering with `instance : HasHtml T := ⟨fun t => ...⟩`
(upstream `__html__`); `Markup.escape`, concatenation, `join` and `format`
then use that rendering instead of escaping. `LeanMarkupsafe.API` has the
same operations with their guarantees in the types (`Escaped`, `SafeArg`).

## Status

Milestone 9: the MarkupSafe surface lean-jinja2 needs, with the theorem
catalogue proved (see CONTRIBUTING.md).

## License

MIT, see [LICENSE](LICENSE). Upstream attribution is in [NOTICE](NOTICE).
