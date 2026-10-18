# Examples: MarkupSafe's own, ported

MarkupSafe ships no example programs, so its examples are the Python code
blocks of its README and docs pages (version 3.0.4). Each is ported 1:1, one
Lean file per page, in the order of upstream's docs (README, then the docs
table of contents: index, escaping, html, formatting). Each file's first
comment names the page, and each block appears with its Python above its
Lean. [`MANIFEST.toml`](MANIFEST.toml) maps every upstream block to its port
(`stack-tools/check-examples.py` checks it), and `tests/Conformance.lean`
checks every value the examples print against MarkupSafe 3.0.4.

| # | Upstream | Lean | Blocks |
|---|---|---|---|
| 1 | `README.md` "Examples" | [`Readme.lean`](Readme.lean) | 1 (10 statements) |
| 2 | `docs/index.rst` | [`Index.lean`](Index.lean) | 1 (5 statements) |
| 3 | `docs/escaping.rst` "Working With Safe Text" (autodoc: the docstrings of `Markup`, `Markup.unescape`, `Markup.striptags`, `escape_silent`, `soft_str`) | [`Escaping.lean`](Escaping.lean) | 7 |
| 4 | `docs/html.rst` "HTML Representations" | [`Html.lean`](Html.lean) | 4 |
| 5 | `docs/formatting.rst` "String Formatting" | [`Formatting.lean`](Formatting.lean) | 3 |
| – | `docs/index.rst` "Installing", `docs/changes.rst`, `docs/license.rst` | excluded: a shell command, the changelog, the license | – |

## Reading the ports

* `Markup(s)` is `Markup.mk s` for a string, and `Markup.of x` for any value
  (an `__html__` object, a number).
* `escape(x)` on a value that may already be markup is `Markup.escape x`;
  `escape s` takes a `String`.
* A class with `__html__` (and `__html_format__`) is a structure with a
  `HasHtml` (`HasHtmlFormat`) instance.
* `t.format(name=v)` is `t.format [("name", v)]`; `t.format(a, b)` is
  `t.format (a, b)`; `t % (a, b)` is `t % (a, b)`; a one-element tuple
  `(a,)` is `[a]`.
* `format` and `%` return `Except FormatError Markup` where Python raises.

## Where the docs and the package disagree

Some printed outputs in the docs differ from what MarkupSafe 3.0.4 prints for
the same code. The ports print, and the conformance suite expects, the
package's output; each file's header says which block:

* `README.md`: `Markup('<strong>hello</strong>')` (the package keeps
  `Hello`).
* `Markup.escape` docstring: `Markup('Hello &lt;em&gt;World&lt;/em&gt;!')`
  (the package keeps the comma).
* `docs/html.rst`: `href="/users/3"` (the class builds `/user/3`).
* `docs/formatting.rst`: the last output lacks its closing `')`.
