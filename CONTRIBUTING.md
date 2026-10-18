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

### Specified on lists, run in place

Every operation that walks its input (`escape`, `unescape`, `striptags`,
`split`, `formatWith`/`format`, `%`, `join`, `*`, and the `int()` literal
grammar of `%d`) is *specified* by a function on `List Char` that recurses once per
character: the right shape for proofs, and the shape every theorem is stated
about. Run as written, that would cost a stack frame and about 24 bytes per
character, and a 24 MB string overflowed the stack. So each has an
executable twin that reads its input in place and builds a `String`:

* `escapeFast`, `collapseFast`, `splitFast`, `joinMarkupFast` are folds;
  `timesFast` and `pyDigitsFast` are accumulator loops;
* `unescapeFast`, `removeTagsFast`, `formatWithFast` (`fmtGo`) and `modFast`
  (`percGo`) walk a `Cursor` (`RepoImpl/Cursor.lean`): positions of a
  `String.Slice`, with `Cursor.rest p` the list the specification sees at
  `p`, used only in proofs and termination measures. Every walker is tail
  recursive. Numeric character references saturate just above U+10FFFF, so a
  reference with millions of digits is still linear.

The fast `str.format` and `%` engines look positional arguments up in an
`Array` and keyword arguments in a `Std.HashMap`, both built once per call
(`renderFieldA`, proved equal to `renderField` on `pos.toArray` and
`namedMap named`). `namedMap` inserts with `insertIfNew`, so the first
binding of a repeated key wins, exactly as `List.lookup` in the
specification (`namedMap_get`). A million `{}`, `{0}`, `{name}` or
`%(name)s` fields are linear. `%d` of text counts
the literal's digits with the in-place `int()` grammar (`pyIntDigitCount`,
the `intStep` fold) before it stores any, so a 20 MB literal over CPython's
4300-digit limit is rejected after one scan.

`split` returns one `Markup` per word, about 80 bytes each: linear, but a
24 MB string of eight million words peaks near 660 MB. That is inherent in
returning a list (upstream returns a Python list of `Markup` too), so the
bench runs it on 5 MB.

Each twin is proved equal to its specification by an `@[csimp]` lemma
(`escape_eq_fast`, `unescape_eq_fast`, `Markup.striptags_eq_fast`,
`Markup.split_eq_fast`, `Markup.formatWith_eq_fast`, `Markup.mod_eq_fast`,
`Markup.joinMarkup_eq_fast`, `Markup.times_eq_fast`, `pyDigits_eq_fast`,
`pyIntLiteral_eq_fast`, `percentIntOfText_eq_fast`;
bundled in `VerifiedExecution`), which makes the compiler run the twin
wherever the specification is called, in this package and in every package
that depends on it. A `@[csimp]` lemma only redirects code compiled after
it, so each one sits right after its definition, before any caller. To add
one: state the twin, prove it equal, mark the lemma `@[csimp]`, add a slot
and a case to `tests/Bench.lean`.

A cursor function that matches on the result of another well-founded
function must have a guard the elaborator cannot see through (an
`if p = s.endPos` first, as in `fieldAt` and `percStep`); otherwise
elaborating the match unfolds the inner function's fixpoint and times out.

`lake exe bench` (run through `stack-tools/capped`) checks the result: 10 to
20 MB of input (or a million items) for each operation, each within 2 s and
300 MB peak resident memory (Linux `VmHWM`).

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

* `VerifiedEscape`: `escape_sound` (output is `IsEscaped`), `unescape_escape`
  (an instance of the `Keel.Codec` law: `escapeCodec` in `Proofs/Codec.lean`
  pairs `escapeChar` with a Keel decoder, `Codec.many` lifts it to strings,
  and `unescape_decode` shows `unescape` is that decoder on escaped text),
  `escape_unescape` (on escaped text), `isEscaped_iff` (escaped text is the
  image of `escape`), `escape_injective`, `escape_markup_id`, `escape_length`
  (exact formula), `softStr_markup`, `escapeSilent_spec`. `escape_injective`
  is `Codec.encode_injective`. `escape_unescape` is proved directly: the
  codec law gives only the decode-after-encode direction.
* `VerifiedClosure` (`formatWith_closed` and `format_closed` among them): `concat_markup_markup`, `concat_escapes`,
  `concat_string_closed`, `join_closed`, `join_markup_closed`,
  `format_closed`, `mod_closed`, `argsSafe_proof`.
* `VerifiedStripTags`: `striptags_no_tags`, `removeTags_no_lt`, `striptags_eq`.
* `VerifiedInterpolation`: `formatWith_interpolates`, `mod_tuple_interpolates`,
  `mod_mapping_interpolates` (for any template, trusted HTML included: the
  output is the template's segments with literals copied, `{{`/`}}`/`%%`
  unquoted, and the `i`-th field replaced by the rendering of the argument
  `fieldRefs` assigns it: automatic fields take positions 0, 1, ... in
  order, `{3}` position 3, `{name}`/`%(name)s` a keyword; a `%` tuple is
  used up exactly), `string_arg_rendering`, and `formatWith_strings` (string
  arguments: one `escape s` per field, `s` the string that field refers to).
  The same statements for `Markup.format` as users call it,
  `format_interpolates`, `format_closed`, `format_strings` and
  `format_keywords`, follow from `Markup.format_eq_formatWith` (`format`
  passes `posOf args` and `namedOf args` to `formatWith`).

The template theory (`Proofs/Template.lean`) is general: `fill_escaped`
says filling an escaped template whose delimiters are token boundaries with
escaped renderings yields escaped text, and `format_closed`/`mod_closed`
are its two instances (`BraceSeg.delimited`, `PercentSeg.delimited`).
Closure under `++` and `join` is `Esc.append`.

**What a `Markup` value means.** `Markup` is trusted, unchecked HTML, as
upstream: `Markup.mk` and `HasHtml` renderings are not checked. Only
`Escaped` (and the `API.*` refinements) carry a proof. `format_closed` and
`mod_closed` cover templates that are themselves escaped text; trusted HTML
templates are covered by the interpolation theorems.

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
  suite checks the fast path agrees with the table, and
  `tests/fixtures/unescape.txt` (10909 cases generated from CPython's
  `html.unescape` by `scripts/gen-unescape-fixture.py`: every HTML5 name in
  three contexts, numeric references around every boundary, random
  reference-heavy strings) must match exactly.
* **Whitespace collapse in `striptags`** (`striptags.whitespace`): that the
  output has no leading, trailing or doubled space and keeps every
  non-space character in order is property-tested. The catalogue's
  `striptags_no_tags` is about tag removal and is proved.

### Deviations from upstream

* **`Markup` is a trusted wrapper, not the refinement.** Upstream
  `Markup("<em>")` marks arbitrary HTML safe, and rendered templates are
  such values, so `Markup` is a structure and the invariant is the subtype
  `Escaped := {m : Markup // IsEscaped m.str}`.
* **Format syntax.** `Markup.format` (and `formatWith`, which takes
  positional and keyword arguments at once) supports literal text, `{{`/`}}` and
  fields `{}`, `{0}`, `{name}` with an optional `:spec` handed to the
  argument (`HasHtmlFormat` sees any spec). `Markup.mod` supports `%%`,
  `%s`, `%d`, `%i` and `%(key)s`. Attribute/index access, `!r`
  conversions, nested specs, Python's string/number format specs, `%`
  flags/widths/precisions and floats return `FormatError.unsupported`.
  A `%(key)` key ends at the first `)` (Python counts nested parentheses).
* **Python object model.** Proxy objects, `str` subclasses and exceptions
  raised by `__html__` have no Lean analogue; `escape(None)` is `"None"`
  upstream, here `Option` goes through `escapeSilent`.
* **`%d` of text** parses it as Python `int()` does (whitespace, sign,
  ASCII digits, single underscores); non-ASCII digits are rejected. `%r`,
  `%a`, `%c` and the float conversions are not supported.
* **Raising variants are opt-in.** `Markup.format!` (panics where upstream
  raises) lives in `LeanMarkupsafe.Raising`, which `import LeanMarkupsafe`
  does not pull in and nothing in the library uses; the gate checks it
  separately.
* **A Lean list on the right of `%` or in `format` is the argument tuple.**
  Python's `Markup('%s') % ['<a>']` formats the list's repr as one value
  (`[&#39;&lt;a&gt;&#39;]`); in Lean `% ["<a>"]` gives `&lt;a&gt;`. A Lean
  list plays the role of Python's tuple, which is how upstream's own
  examples read (`% ("foo & bar",)` is `% ["foo & bar"]`). FormatArg has no
  repr, so there is no Python-list value to format.
* **Positional `%s` with a mapping.** Upstream `Markup("%s") % {"a": 1}`
  renders the mapping's `repr`; a `FormatArg` mapping has no `repr`, so
  this returns `FormatError.unsupported`. Mixing `%(a)s` and `%s` with a
  mapping is a `TypeError` upstream and an error here.
* **Concatenation is wider than upstream.** `Markup.concat m x` accepts any
  `ToMarkup` value, including numbers through `toString`, where upstream
  `Markup + 1` raises `TypeError`. The result is still escaped.
* **Huge numeric references.** A decimal reference over 4300 digits decodes
  to U+FFFD like any out-of-range value; CPython raises `ValueError` from its
  integer string conversion limit.
* **Error texts.** `FormatError.mixedNumbering` gives one message for both
  directions of mixing `{}` and `{0}`; upstream words the two differently.
* **`str` method wrappers** other than `split` and `*` (`splitlines`,
  `partition`, `strip`, `replace`, ...) are not ported; use `String`
  functions on `m.str` and `Markup.mk`.

## Tests

* `tests/Props.lean`: seeded property tests, no dependencies, under a second.
* `tests/Conformance.lean`: cases re-expressed from the upstream suite; each
  names the upstream test (`tests/test_x.py::test_y`).
* `tests/Bench.lean`: big inputs (`lake exe bench`): time and peak-memory
  bounds for every operation that walks its input.
* `tests/pbt/`: a separate Lake package, the one place an external dependency
  (`plausible`) is taken.

## Traceability

`docs/traceability.toml` links upstream behaviour to the Lean symbol, theorem
and test that realise it. Add a row when behaviour is newly implemented,
tested-only, excluded, or deviates. CI fails if a registered symbol does not
resolve.

## Conventions

* Lean 4 `leanprover/lean4:v4.35.0`; no Mathlib; the core library depends only on Lean
  core and lean-keel (the shared theory library, `Keel.Codec`), pinned by
  commit in `lake-manifest.json`.
* Choose the definition that suits the automation over a prettier one with a
  harder proof.
* No upstream code is copied; the upstream test suite and docs are the spec.
