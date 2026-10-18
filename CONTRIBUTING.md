# Contributing to lean-markupsafe

`README.md` covers usage. This file covers the architecture, the verification
rules, the repository layout and the conventions, and is the document to keep
current when the code changes.

## Architecture

`LeanMarkupsafe/` is layered bottom-up; each layer imports only the ones below it, so a
proof at one layer rewrites with lemmas from beneath it instead of unfolding
to bytes:

| Directory | Holds | Proved? |
|---|---|---|
| `DataTypes/` | structures and inductives; invariants are fields | n/a |
| `RepoImpl/` | executable definitions; total, structural recursion | subject of proofs |
| `Specifications/` | the properties, in `Prop` | the contract |
| `Proofs/` | theorems; `Proofs/Verified.lean` bundles one `Verified<Layer>` per layer | yes |
| `APIs/` | the public surface, returning refinements | by construction |
| `Transport.lean` (if present) | the only effectful module | no; tested |

Everything except the transport module is a pure function. This is
load-bearing: a round-trip property of a function is an equation that
`omega` and `simp` attack directly; the same property of a procedure would
be a Hoare triple over a heap.

## Verification <a name="verification"></a>

* **Weak preconditions, strong postconditions.** A public function takes the
  minimal hypothesis its body needs (usually none; the refinement lives in the
  input type) and returns the strongest useful statement, typically a round
  trip or a membership, as `{r // Post r}` or `Except Err {r // Post r}`.
* **Refinement types are subtypes with `Decidable` predicates**, so the same
  predicate is checked at runtime (`if h : P x`) and used in proofs.
* **Totality.** No `partial def` or `unsafe` under `LeanMarkupsafe/`. Byte parsers recurse
  on a `Nat` fuel equal to the remaining input, with a progress lemma per
  production.
* **`_ext` lemmas.** A decoder lemma holds on any continuation of the buffer and
  reports the final position, so field lemmas compose. Do not add a lemma that
  only holds at the end of a buffer; it is unusable one field later.
* **Numbers.** `Nat`/`Int`/decimal-as-rational in proofs. `Float` only at the
  boundary via `Float.toBits`. Never `bv_decide` or `native_decide`.
* **The gate.** `scripts/check.sh` runs what CI runs: build, `sorry` grep,
  `scripts/Axioms.lean` (every theorem under `LeanMarkupsafe` reaches only `propext`,
  `Quot.sound`, `Classical.choice`), `lake exe props`, `lake exe conformance`,
  the traceability check.

### What is proved

`Proofs/Verified.lean` bundles every headline property:

* `VerifiedEscape`: `escape_sound` (output is `IsEscaped`), `unescape_escape`,
  `escape_unescape` (on escaped text), `isEscaped_iff` (escaped text is the
  image of `escape`), `escape_injective`, `escape_markup_id`, `escape_length`
  (exact formula), `softStr_markup`, `escapeSilent_spec`.
* `VerifiedClosure`: `concat_markup_markup`, `concat_escapes`,
  `concat_string_closed`, `join_closed`, `join_markup_closed`,
  `format_closed`, `mod_closed`, `argsSafe_proof`.
* `VerifiedStripTags`: `striptags_no_tags`, `removeTags_no_lt`, `striptags_eq`.

`IsEscaped s` (`Specifications/Basic.lean`) says `s` is a sequence of
characters other than `& < > " '` and the five references `escape` emits.
`IsEscaped` is decidable (through `esc_iff_roundtrip`).

### Tested, not proved

Listed here with the reason, and in `docs/traceability.toml` with
`status = "tested"`.

* **`unescape` on arbitrary references** (`unescape.html5`). Decoding goes
  through the 2231-entry HTML5 table, the longest-prefix fallback and the
  WHATWG invalid-reference tables. The proofs only need the five references
  `escape` emits, which take a fast path in `lookupNamed`; the conformance
  suite checks the fast path agrees with the table, and the numeric and
  fallback behaviour against cases taken from Python's `html.unescape`.
* **Whitespace collapse in `striptags`** (`striptags.whitespace`): that the
  output has no leading, trailing or doubled space and keeps every
  non-space character in order is property-tested. The catalogue's
  `striptags_no_tags` is about tag removal and is proved.

### Deviations from upstream

* **`Markup` is a trusted wrapper, not the refinement.** Upstream
  `Markup("<em>")` marks arbitrary HTML safe, and rendered templates are
  such values, so `Markup` is a structure and the invariant is the subtype
  `Escaped := {m : Markup // IsEscaped m.str}`.
* **Format syntax.** `Markup.format` supports literal text, `{{`/`}}` and
  fields `{}`, `{0}`, `{name}` with an optional `:spec` handed to the
  argument (`HasHtmlFormat` sees any spec). `Markup.mod` supports `%%`,
  `%s`, `%d`, `%i` and `%(key)s`. Attribute/index access, `!r`
  conversions, nested specs, Python's string/number format specs, `%`
  flags/widths/precisions and floats return `FormatError.unsupported`.
  A `%(key)` key ends at the first `)` (Python counts nested parentheses).
* **Python object model.** Proxy objects, `str` subclasses and exceptions
  raised by `__html__` have no Lean analogue; `escape(None)` is `"None"`
  upstream, here `Option` goes through `escapeSilent`.
* **`str` method wrappers** other than `split` and `*` (`splitlines`,
  `partition`, `strip`, `replace`, ...) are not ported; use `String`
  functions on `m.str` and `Markup.mk`.

## Tests

* `tests/Props.lean`: seeded property tests, no dependencies, under a second.
* `tests/Conformance.lean`: cases re-expressed from the upstream suite; each
  names the upstream test (`tests/test_x.py::test_y`).
* `tests/pbt/`: a separate Lake package, the one place an external dependency
  (`plausible`) is taken.

## Traceability

`docs/traceability.toml` links upstream behaviour to the Lean symbol, theorem
and test that realise it. Add a row when behaviour is newly implemented,
tested-only, excluded, or deviates. CI fails if a registered symbol does not
resolve.

## Conventions

* Lean 4 `leanprover/lean4:v4.35.0`; no Mathlib; the core library depends only on Lean
  core and the sibling `lean-*` repos listed in `lakefile.toml`, pinned by
  commit in `lake-manifest.json`.
* Choose the definition that suits the automation over a prettier one with a
  harder proof.
* No upstream code is copied; the upstream test suite and docs are the spec.
