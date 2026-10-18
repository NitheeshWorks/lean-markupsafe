# lean-markupsafe

[![Lean 4](https://img.shields.io/badge/built%20with-Lean%204-blue.svg)](https://lean-lang.org)
[![Proofs](https://img.shields.io/badge/proofs-machine%20checked-brightgreen.svg)](CONTRIBUTING.md#verification)

A clean-room port of [MarkupSafe](https://github.com/pallets/markupsafe) to
Lean 4, with machine-checked proofs.

MarkupSafe implements a text object that escapes characters so it is safe to
use in HTML and XML. Characters that have special meanings are replaced so
that they display as the actual characters. This mitigates injection attacks,
meaning untrusted user input can safely be displayed on a page.

## Examples

The upstream README's examples, translated:

```lean
import LeanMarkupsafe
open LeanMarkupsafe

-- escape replaces special characters and wraps in Markup
#eval escape "<script>alert(document.cookie);</script>"
-- Markup.mk "&lt;script&gt;alert(document.cookie);&lt;/script&gt;"

-- wrap in Markup to mark text "safe" and prevent escaping
#eval Markup.mk "<strong>Hello</strong>"
-- Markup.mk "<strong>Hello</strong>"

#eval Markup.escape (Markup.mk "<strong>Hello</strong>")
-- Markup.mk "<strong>Hello</strong>"

-- methods and operators escape their arguments
def template := Markup.mk "Hello <em>{name}</em>"
#eval template.format [("name", "\"World\"")]
-- Except.ok (Markup.mk "Hello <em>&#34;World&#34;</em>")

#eval Markup.mk "<em>Hello</em> " ++ "<foo>"
-- Markup.mk "<em>Hello</em> &lt;foo&gt;"
#eval Markup.mk "<em>%s</em>" % "foo & bar"
-- Except.ok (Markup.mk "<em>foo &amp; bar</em>")
#eval Markup.mk "<em>%s:%s</em>" % ("<foo>", "<bar>")
-- Except.ok (Markup.mk "<em>&lt;foo&gt;:&lt;bar&gt;</em>")
#eval (Markup.mk "Main &raquo;\t<em>About</em>").striptags
-- "Main » About"
```

More examples, ported one for one from MarkupSafe's docs pages, are in
[`examples/`](examples/README.md).

A type opts into safe rendering with `instance : HasHtml T := ⟨fun t => ...⟩`
(upstream `__html__`), or `HasHtmlFormat` for `__html_format__`.
`Markup.escape`, `++`, `join`, `format` and `%` then use its rendering
instead of escaping it. `Markup.of x` is upstream's `Markup(x)`. `format`
and `%` return `Except FormatError Markup` where upstream raises; `format!`
panics instead, for code that must return `Markup`. `t.format` takes a value,
a tuple, a list, or a list of `(key, value)` pairs (keyword arguments);
`formatWith pos named` takes both at once.

## What a `Markup` value means

As upstream, `Markup` is trusted, unchecked HTML: `Markup.mk s` (upstream
`Markup(s)`) marks any string safe, and a `HasHtml` rendering is used
verbatim. A `Markup` value is not a proof that anything was escaped. The
proved guarantees are carried by:

* `Escaped := {m : Markup // IsEscaped m.str}`: markup proved to be escaped
  text (no raw `< > " '`, every `&` starting `&amp; &lt; &gt; &#34; &#39;`).
* the `LeanMarkupsafe.API` functions, which return refinements;
* for trusted HTML templates such as `<em>{}</em>`, the interpolation
  theorems below and `API.formatTrusted`, `API.formatStrings`,
  `API.modTrusted`, `API.modStrings`, whose return types say exactly what
  the output is.

A templating engine (lean-jinja2) should keep untrusted text as `String`,
build output with `escape`, `++` and `API.formatStrings`, and treat any
`Markup` it receives as trusted.

## What is proved

All in `LeanMarkupsafe/Proofs/`, bundled in `Proofs/Verified.lean`:

| Theorem | In words | Statement |
|---|---|---|
| `escape_sound` | escaping yields escaped text | `IsEscaped (escape s).str` |
| `escapeCodec` (a lawful `Keel.Codec`) | escaping is the encoder of a lawful codec whose decoder is `unescape` on escaped text | `escapeCodec.encode s = (escape s).str.toList` |
| `unescape_escape` | unescaping undoes escaping (an instance of the codec law `Codec.decode_encode`) | `unescape (escape s).str = s` |
| `escape_unescape` | on escaped text, escaping undoes unescaping | `IsEscaped s → (escape (unescape s)).str = s` |
| `isEscaped_iff` | escaped text is exactly what `escape` produces | `IsEscaped s ↔ ∃ t, (escape t).str = s` |
| `escape_injective` | escaping loses nothing (an instance of `Codec.encode_injective`) | `escape s = escape t → s = t` |
| `escape_markup_id` | markup is not escaped again | `Markup.escape m = m` |
| `escape_length` | exact length | `(escape s).str.length = s.length + 4·#& + 3·#< + 3·#> + 4·#" + 4·#'` |
| `concat_markup_markup`, `join_closed`, … | concatenation and `join` keep text escaped | `IsEscaped a.str → IsEscaped b.str → IsEscaped (a ++ b).str` |
| `format_eq_formatWith` | `format` passes its arguments' positional and keyword lists to `formatWith` | `t.format args = t.formatWith (posOf args) (namedOf args)` |
| `format_interpolates` | for any template, `format` replaces the `i`-th field by the rendering of the argument it names, and changes nothing else | `t.format args = .ok r → Interpolates BraceSeg (posOf args) (namedOf args) t r` |
| `mod_tuple_interpolates`, `mod_mapping_interpolates` | the same for `%`; a tuple is used up exactly | `t.mod (.tuple xs) = .ok r → InterpolatesAll PercentSeg xs t r` |
| `format_strings`, `format_keywords` | with string arguments (`t.format ss`, `t.format [("k", s)]`) every field becomes `escape` of the string it names | `t.format ss = .ok r → ∃ segs args, … ∧ r.str = String.ofList (fillSegs segs (args.map escape))` |
| `fill_escaped` → `format_closed`, `mod_closed` | an escaped template with safe arguments gives escaped text | `IsEscaped t.str → … → IsEscaped r.str` |
| `striptags_no_tags` | no complete tag survives tag removal | `NoCompleteTag (removeTags l)` |
| `escape_eq_fast`, `unescape_eq_fast`, `Markup.formatWith_eq_fast`, … | what runs is what is specified: each in-place implementation (constant stack, linear time) is the list-based specification, and runs in its place via `@[csimp]` | `@escape = @escapeFast` |

What is tested rather than proved, and every deviation from upstream, is in
[CONTRIBUTING.md](CONTRIBUTING.md#verification) and `docs/traceability.toml`.

## Getting started

```
lake build            # library, proofs, and both test executables
lake exe props        # property tests (seeded; `lake exe props 42`)
lake exe conformance  # cases re-expressed from the upstream test suite
lake exe bench        # 20 MB inputs: time and memory bounds
scripts/check.sh      # the whole CI gate, locally
```

Toolchain: `leanprover/lean4:v4.35.0` (pinned in `lean-toolchain`; `elan` installs it).

Part of the verified FastAPI stack: [lean-fastapi](https://github.com/NitheeshWorks/lean-fastapi)
and its dependencies, each ported as its own repo with its proofs. This one
depends on [lean-keel](https://github.com/NitheeshWorks/lean-keel), the
stack's shared theory library (`Keel.Codec`).

## License

MIT, see [LICENSE](LICENSE). Upstream attribution is in [NOTICE](NOTICE).
