/-!
# DataTypes

The types every other layer is written against. This module is part of the
stable public API: `lean-jinja2` and other dependents build on `Markup`,
`HasHtml` and `FormatArg`.

* `Markup` is a string marked safe for insertion into HTML. Upstream's
  `Markup(s)` constructor trusts its argument without escaping it, and so
  does `Markup.mk`/`Markup.markSafe`. The refinement that says a value
  really is escaped text (`IsEscaped`, `Escaped`) lives in
  `Specifications/Basic.lean`; every value `escape` produces satisfies it
  (`escape_sound`).
* `HasHtml` is upstream's `__html__` protocol: a type that knows its own safe
  HTML rendering opts in with an instance. `HasHtmlFormat` is
  `__html_format__`, the same with a format specification.
* `FormatArg` is one argument to `Markup.format`/`Markup.mod`: how it renders
  under each conversion, already escaped.
-/

namespace LeanMarkupsafe

/-- A string that is safe to insert into an HTML or XML document, either
because it was escaped or because it was marked safe. Constructing one with
`Markup.mk` (upstream `Markup(s)`) trusts the argument; use `escape` to
produce one from untrusted text. -/
structure Markup where
  /-- Mark a string as safe without escaping it (upstream `Markup(s)`). -/
  mk ::
  /-- The underlying text (upstream `str(markup)`). -/
  str : String
  deriving DecidableEq, Hashable, Ord, Inhabited

namespace Markup

/-- The empty markup (upstream `Markup()`). -/
def empty : Markup := ⟨""⟩

/-- Mark a string as safe without escaping it. Same as `Markup.mk`; the name
says what the call asserts. -/
def markSafe (s : String) : Markup := ⟨s⟩

instance : ToString Markup := ⟨Markup.str⟩

/-- Shown as the Lean expression that builds it, as upstream shows
`Markup('...')`. -/
instance : Repr Markup where
  reprPrec m p := Repr.addAppParen ("Markup.mk " ++ repr m.str) p
instance : EmptyCollection Markup := ⟨empty⟩

/-- Concatenation of two markups: both sides are already safe, so nothing is
escaped. Concatenation with a plain string escapes the string; see the
`HAppend` instances in `RepoImpl/Escape.lean`. -/
def append (a b : Markup) : Markup := ⟨a.str ++ b.str⟩

instance : Append Markup := ⟨append⟩

@[simp] theorem str_append (a b : Markup) : (a ++ b).str = a.str ++ b.str := rfl
@[simp] theorem str_empty : empty.str = "" := rfl
@[simp] theorem str_markSafe (s : String) : (markSafe s).str = s := rfl

end Markup

/-- Upstream's `__html__` protocol: a type that renders itself as safe HTML.
`escape`-like operations (`Markup.escape`, concatenation, `join`, `format`)
use this rendering verbatim instead of escaping the value's text. -/
class HasHtml (α : Type u) where
  /-- The value's safe HTML rendering (upstream `obj.__html__()`). -/
  html : α → Markup

/-- A `Markup` renders as itself (upstream `Markup.__html__` returns `self`). -/
instance : HasHtml Markup := ⟨id⟩

/-- Why a `format` or `%` interpolation failed. Upstream raises `TypeError`,
`ValueError`, `KeyError` or `IndexError`; the constructor names the case and
`toString` gives upstream's message. -/
inductive FormatError where
  /-- `%` with fewer arguments than placeholders (`TypeError`). -/
  | notEnoughArguments
  /-- `%` with more arguments than placeholders (`TypeError`). -/
  | notAllConverted
  /-- `%(key)s` against positional arguments (`TypeError`). -/
  | requiresMapping
  /-- A named field with no such argument (`KeyError`). -/
  | missingKey (key : String)
  /-- A positional field past the end of the arguments (`IndexError`). -/
  | indexOutOfRange (index : Nat)
  /-- Mixed `{}` and `{0}` in one template (`ValueError`). -/
  | mixedNumbering
  /-- A malformed template: unmatched brace, incomplete `%` (`ValueError`). -/
  | badTemplate (msg : String)
  /-- A conversion the argument does not support, e.g. `%d` of a string
  (`TypeError`). -/
  | typeError (msg : String)
  /-- A format specification the argument does not support (`ValueError`). -/
  | unsupportedSpec (msg : String)
  /-- Template syntax upstream accepts that this port does not implement
  (attribute/index access, `!r` conversions, `%` flags and widths); see the
  deviations in `docs/traceability.toml`. -/
  | unsupported (what : String)
  deriving DecidableEq, Repr, Inhabited

instance : ToString FormatError where
  toString
    | .notEnoughArguments => "not enough arguments for format string"
    | .notAllConverted => "not all arguments converted during string formatting"
    | .requiresMapping => "format requires a mapping"
    | .missingKey k => s!"KeyError: '{k}'"
    | .indexOutOfRange i => s!"Replacement index {i} out of range for positional args tuple"
    | .mixedNumbering =>
        "cannot switch between automatic field numbering and manual field specification"
    | .badTemplate m => m
    | .typeError m => m
    | .unsupportedSpec m => m
    | .unsupported w => s!"unsupported by lean-markupsafe: {w}"

/-- How a placeholder asks an argument to render. -/
inductive Conversion where
  /-- `%s`. -/
  | percentStr
  /-- `%d` or `%i`. -/
  | percentInt
  /-- `{...:spec}` in `Markup.format`; the empty spec for a bare `{}`. -/
  | brace (spec : String)
  deriving DecidableEq, Repr, Inhabited

/-- One argument to `Markup.format`/`Markup.mod`: its rendering under each
conversion. The rendering is the final, safe text; the formatter inserts it
verbatim. Build one with `FormatArg.ofString`, `ofMarkup`, `ofHtml`, `ofInt`
or `ToFormatArg.toFormatArg`. -/
structure FormatArg where
  /-- Render under a conversion, or fail as upstream would. -/
  render : Conversion → Except FormatError Markup

/-- Upstream's `__html_format__` protocol: a type that renders itself as
safe HTML under a format specification (`"{0:link}"`). `Markup.format` calls
it for every field of a value with this instance, the empty specification
included. -/
class HasHtmlFormat (α : Type u) extends HasHtml α where
  /-- The rendering under a format specification (upstream
  `obj.__html_format__(spec)`). -/
  htmlFormat : α → String → Except FormatError Markup

/-- The arguments of a `%` interpolation (upstream `Markup.__mod__`): a tuple
of positional arguments (a single value is a one-element tuple), or a mapping
for `%(key)s` fields. -/
inductive PercentArgs where
  | tuple (args : List FormatArg)
  | mapping (args : List (String × FormatArg))

/-- The result of upstream `soft_str`: a `Markup` stays a `Markup` (so it will
not be escaped again), anything else becomes plain text. -/
inductive SoftString where
  | plain (s : String)
  | markup (m : Markup)
  deriving DecidableEq, Repr, Inhabited

/-- The text of a `SoftString`, forgetting whether it was marked safe. -/
def SoftString.toString : SoftString → String
  | .plain s => s
  | .markup m => m.str

instance : ToString SoftString := ⟨SoftString.toString⟩

end LeanMarkupsafe
