import LeanMarkupsafe.RepoImpl

/-!
# Specifications

The properties, stated in `Prop`, in terms of `DataTypes` and `RepoImpl`.
Nothing here is proved; this is the contract. Each headline property is a
`def ... : Prop` in `LeanMarkupsafe.Spec`, proved in `Proofs/` and bundled
in `Proofs/Verified.lean`.

## `IsEscaped`

`Esc l` holds when `l` is a sequence of *tokens*, each either a character
other than `& < > " '`, or one of the five references `escape` emits
(`&amp; &lt; &gt; &#34; &#39;`). So an escaped string has no raw `<`, `>`,
`"` or `'`, and every `&` starts one of the five references. This is exactly
the image of `escape` (`Spec.isEscapedIffImage`), and `escape ∘ unescape` is
the identity on it.
-/

namespace LeanMarkupsafe

/-- The five characters `escape` replaces. -/
def isSpecial (c : Char) : Bool :=
  c == '&' || c == '<' || c == '>' || c == '"' || c == '\''

/-- The five references `escape` emits. -/
def entities : List (List Char) :=
  [['&', 'a', 'm', 'p', ';'], ['&', 'l', 't', ';'], ['&', 'g', 't', ';'],
   ['&', '#', '3', '4', ';'], ['&', '#', '3', '9', ';']]

/-- Characters that occur inside one of the five references after its `&`.
Any other non-special character is a token boundary in an escaped string. -/
def isEntityChar (c : Char) : Bool :=
  ['a', 'm', 'p', ';', 'l', 't', 'g', '#', '3', '4', '9'].contains c

/-- A character list is a sequence of safe characters and the five
references `escape` emits. -/
inductive Esc : List Char → Prop where
  | nil : Esc []
  | char {c : Char} {l : List Char} : isSpecial c = false → Esc l → Esc (c :: l)
  | ent {e l : List Char} : e ∈ entities → Esc l → Esc (e ++ l)

/-- The refinement on `Markup`: the text is escaped text, with no raw
`< > " '` and every `&` starting one of `&amp; &lt; &gt; &#34; &#39;`. -/
def IsEscaped (s : String) : Prop := Esc s.toList

/-- Markup that is escaped text: what `escape` returns, closed under
concatenation, `join`, `format` and `%`. -/
abbrev Escaped := {m : Markup // IsEscaped m.str}

/-- A format argument is safe when every rendering it produces is escaped
text. Strings, integers and escaped markup are safe. -/
def FormatArg.Safe (a : FormatArg) : Prop :=
  ∀ c m, a.render c = .ok m → IsEscaped m.str

/-- Whether a list beginning after `<` opens a tag or comment that is never
closed (so `removeTags` stops and keeps it). -/
def OpensUnclosed (l : List Char) : Prop :=
  if l.take 3 = ['!', '-', '-'] then findCommentEnd (l.drop 3) = none
  else findClose l = none

/-- No complete tag survives: the text has no `<`, except possibly one that
begins an unclosed tag or comment, after which the scan stopped. -/
inductive NoCompleteTag : List Char → Prop where
  | nil : NoCompleteTag []
  | cons {c : Char} {l : List Char} : c ≠ '<' → NoCompleteTag l → NoCompleteTag (c :: l)
  | unclosed {l : List Char} : OpensUnclosed l → NoCompleteTag ('<' :: l)

/-- The length `escape` produces: four extra characters per `&`, `"` and
`'`, three per `<` and `>`. -/
def escapedLength (s : String) : Nat :=
  s.length + 4 * s.toList.count '&' + 3 * s.toList.count '<' + 3 * s.toList.count '>' +
    4 * s.toList.count '"' + 4 * s.toList.count '\''

/-! ## Templates

A model of templates independent of the engines. A template is a list of
segments: a literal character, a quoted delimiter (`{{`, `}}`, `%%`) or a
field. `printSegs` gives the template text. `fieldRefs` says which argument
each field draws on: automatic fields (`{}`, `%s`) take positions 0, 1, 2, ...
in order, `{3}` takes position 3, `{name}` and `%(name)s` take a keyword.
`fillSegs` gives the output once each field is replaced by a rendering.
The interpolation theorems say that `format` and `%` compute exactly this. -/

/-- `Forall₂ R as bs`: the lists have the same length and `R` relates their
elements pairwise, in order. -/
inductive Forall₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : Forall₂ R [] []
  | cons {a b as bs} : R a b → Forall₂ R as bs → Forall₂ R (a :: as) (b :: bs)

/-- One segment of a template. -/
inductive Seg where
  /-- A literal character, copied verbatim. -/
  | text (c : Char)
  /-- A quoted delimiter: printed as `src`, yields `c` (`{{` gives `{`). -/
  | quote (src : List Char) (c : Char)
  /-- A placeholder printed as `src`, naming an argument and a conversion. -/
  | field (src : List Char) (name : FieldName) (conv : Conversion)

/-- The template text of a segment. -/
def Seg.src : Seg → List Char
  | .text c => [c]
  | .quote s _ => s
  | .field s _ _ => s

/-- The template text of a segment list. -/
def printSegs : List Seg → List Char
  | [] => []
  | s :: r => s.src ++ printSegs r

/-- The argument and conversion of each field, numbering automatic fields
from `n`. -/
def fieldRefsFrom : Nat → List Seg → List (ArgRef × Conversion)
  | _, [] => []
  | n, .field _ fn c :: r => (fn.ref n, c) :: fieldRefsFrom (fn.next n) r
  | n, _ :: r => fieldRefsFrom n r

/-- The argument and conversion of each field, in order. -/
def fieldRefs (segs : List Seg) : List (ArgRef × Conversion) := fieldRefsFrom 0 segs

/-- Number of fields. -/
def fieldCount : List Seg → Nat
  | [] => 0
  | .field _ _ _ :: r => fieldCount r + 1
  | _ :: r => fieldCount r

/-- Number of automatic fields. -/
def autoCount : List Seg → Nat
  | [] => 0
  | .field _ .auto _ :: r => autoCount r + 1
  | _ :: r => autoCount r

/-- The output: literals copied, quotes unquoted, fields replaced in order
by the given renderings. -/
def fillSegs : List Seg → List Markup → List Char
  | [], _ => []
  | .text c :: r, ms => c :: fillSegs r ms
  | .quote _ c :: r, ms => c :: fillSegs r ms
  | .field _ _ _ :: r, m :: ms => m.str.toList ++ fillSegs r ms
  | .field _ _ _ :: r, [] => fillSegs r []

/-- A well-formed `str.format` segment: literal text has no brace, quotes
are `{{`/`}}`, a field is `{name:spec}` with no brace inside, naming the
argument its name parses to and passing its spec. -/
def BraceSeg : Seg → Prop
  | .text c => c ≠ '{' ∧ c ≠ '}'
  | .quote s c => (s = ['{', '{'] ∧ c = '{') ∨ (s = ['}', '}'] ∧ c = '}')
  | .field s fn conv => ∃ f, s = '{' :: f ++ ['}'] ∧ '{' ∉ f ∧ '}' ∉ f ∧
      parseFieldName (splitField f).1 = .ok fn ∧ conv = .brace (String.ofList (splitField f).2)

/-- A well-formed `%` segment: literal text has no `%`, the quote is `%%`, a
field is `%c` (automatic) or `%(key)c` with no `)` in the key, where `c` is
a supported conversion character. -/
def PercentSeg : Seg → Prop
  | .text c => c ≠ '%'
  | .quote s c => s = ['%', '%'] ∧ c = '%'
  | .field s fn conv => ∃ cv, percentConv cv = .ok conv ∧
      ((s = ['%', cv] ∧ fn = .auto) ∨
       ∃ k, ')' ∉ k ∧ s = '%' :: '(' :: k ++ [')', cv] ∧ fn = .key (String.ofList k))

/-- `ms` are the renderings of the template's fields: the `i`-th is what the
argument the `i`-th field refers to renders to under that field's
conversion. -/
def Fills (pos : List FormatArg) (named : List (String × FormatArg)) (segs : List Seg)
    (ms : List Markup) : Prop :=
  Forall₂ (fun rc m => ∃ a, rc.1.lookup pos named = some a ∧ a.render rc.2 = .ok m)
    (fieldRefs segs) ms

/-- `r` is template `t` with each field replaced by the rendering of the
argument it refers to, and nothing else changed. -/
def Interpolates (wf : Seg → Prop) (pos : List FormatArg) (named : List (String × FormatArg))
    (t r : Markup) : Prop :=
  ∃ segs ms, (∀ s ∈ segs, wf s) ∧ printSegs segs = t.str.toList ∧ Fills pos named segs ms ∧
    r.str.toList = fillSegs segs ms

/-- `Interpolates` for `%` with a tuple, which must use every argument. -/
def InterpolatesAll (wf : Seg → Prop) (xs : List FormatArg) (t r : Markup) : Prop :=
  ∃ segs ms, (∀ s ∈ segs, wf s) ∧ printSegs segs = t.str.toList ∧ Fills xs [] segs ms ∧
    r.str.toList = fillSegs segs ms ∧ autoCount segs = xs.length

/-- The string a reference names, for string arguments. -/
def ArgRef.lookupStr (ss : List String) (kv : List (String × String)) : ArgRef → Option String
  | .pos i => ss[i]?
  | .key k => kv.lookup k

namespace Spec

/-- `escape_sound`: everything `escape` returns is escaped text. -/
def escapeSound : Prop := ∀ s : String, IsEscaped (escape s).str

/-- `unescape_escape`: unescaping undoes escaping. -/
def unescapeEscape : Prop := ∀ s : String, unescape (escape s).str = s

/-- `escape_unescape`: on escaped text, escaping undoes unescaping. -/
def escapeUnescape : Prop := ∀ s : String, IsEscaped s → (escape (unescape s)).str = s

/-- `isEscaped_iff`: escaped text is exactly the image of `escape`. -/
def isEscapedIffImage : Prop := ∀ s : String, IsEscaped s ↔ ∃ t, (escape t).str = s

/-- `escape_injective`. -/
def escapeInjective : Prop := ∀ s t : String, escape s = escape t → s = t

/-- `escape_markup_id`: escaping markup returns it unchanged. -/
def escapeMarkupId : Prop := ∀ m : Markup, Markup.escape m = m

/-- `escape_length`: the exact length of the escaped text. -/
def escapeLength : Prop := ∀ s : String, (escape s).str.length = escapedLength s

/-- `concat_markup_markup`: concatenation preserves the invariant. -/
def appendClosed : Prop :=
  ∀ a b : Markup, IsEscaped a.str → IsEscaped b.str → IsEscaped (a ++ b).str

/-- Concatenating a plain string escapes it, on either side. -/
def concatEscapes : Prop :=
  ∀ (m : Markup) (s : String),
    (m ++ s).str = m.str ++ (escape s).str ∧ (s ++ m).str = (escape s).str ++ m.str

/-- Concatenating escaped markup with a plain string stays escaped. -/
def concatStringClosed : Prop :=
  ∀ (m : Markup) (s : String), IsEscaped m.str → IsEscaped (m ++ s).str ∧ IsEscaped (s ++ m).str

/-- `join` with an escaped separator over strings is escaped. -/
def joinClosed : Prop :=
  ∀ (sep : Markup) (xs : List String), IsEscaped sep.str → IsEscaped (Markup.join sep xs).str

/-- `join` over markup items stays escaped when the separator and every item
are. -/
def joinMarkupClosed : Prop :=
  ∀ (sep : Markup) (xs : List Markup),
    IsEscaped sep.str → (∀ x ∈ xs, IsEscaped x.str) → IsEscaped (Markup.join sep xs).str

/-- `format` of an escaped-text template with safe arguments is escaped.
This covers templates that are themselves escaped text only (no raw `<`);
for trusted HTML templates see `formatInterpolates`. -/
def formatClosed : Prop :=
  ∀ (t : Markup) (pos : List FormatArg) (named : List (String × FormatArg)) (r : Markup),
    IsEscaped t.str → (∀ a ∈ pos, a.Safe) → (∀ p ∈ named, p.2.Safe) →
    t.formatWith pos named = .ok r → IsEscaped r.str

/-- `%` of an escaped-text template with safe arguments is escaped. This
covers templates that are themselves escaped text only; for trusted HTML
templates see `modTupleInterpolates`. -/
def modClosed : Prop :=
  ∀ (t : Markup) (xs : List FormatArg) (kv : List (String × FormatArg)) (r : Markup),
    IsEscaped t.str → (∀ a ∈ xs, a.Safe) → (∀ p ∈ kv, p.2.Safe) →
    (t.mod (.tuple xs) = .ok r ∨ t.mod (.mapping kv) = .ok r) → IsEscaped r.str

/-- String, integer and escaped-markup arguments are safe. -/
def argsSafe : Prop :=
  (∀ s, (FormatArg.ofString s).Safe) ∧ (∀ i, (FormatArg.ofInt i).Safe) ∧
    (∀ n, (FormatArg.ofNat n).Safe) ∧ (∀ m : Markup, IsEscaped m.str → (FormatArg.ofMarkup m).Safe)

/-- `striptags_no_tags`: after tag removal no complete tag is left. -/
def striptagsNoTags : Prop := ∀ l : List Char, NoCompleteTag (removeTags l)

/-- `striptags` is tag removal, whitespace collapse, then `unescape`. -/
def striptagsEq : Prop :=
  ∀ m : Markup, m.striptags = unescape (String.ofList (collapseSpaces (removeTags m.str.toList)))

/-- Text without `<` passes tag removal unchanged. -/
def removeTagsNoLt : Prop := ∀ l : List Char, '<' ∉ l → removeTags l = l

/-- `soft_str` keeps markup as markup, so escaping it again is the identity. -/
def softStrMarkup : Prop :=
  ∀ m : Markup, Markup.escape (softStr m) = m ∧ Markup.escape (softStr m.str) = escape m.str

/-- `escape_silent` maps `none` to the empty markup and agrees with
`Markup.escape` otherwise. -/
def escapeSilentSpec : Prop :=
  escapeSilent (none : Option String) = Markup.empty ∧
    ∀ s : String, escapeSilent (some s) = escape s

/-- `format_interpolates`: for any template, trusted HTML included, a
successful `format` is the template with each field replaced by the
rendering of the argument it refers to. -/
def formatInterpolates : Prop :=
  ∀ (t : Markup) (pos : List FormatArg) (named : List (String × FormatArg)) (r : Markup),
    t.formatWith pos named = .ok r → Interpolates BraceSeg pos named t r

/-- `mod_tuple_interpolates`: the same for `%` with a tuple; every argument
is used. -/
def modTupleInterpolates : Prop :=
  ∀ (t : Markup) (xs : List FormatArg) (r : Markup),
    t.mod (.tuple xs) = .ok r → InterpolatesAll PercentSeg xs t r

/-- `mod_mapping_interpolates`: the same for `%` with a mapping. -/
def modMappingInterpolates : Prop :=
  ∀ (t : Markup) (kv : List (String × FormatArg)) (r : Markup),
    t.mod (.mapping kv) = .ok r → Interpolates PercentSeg [] kv t r

/-- A string argument renders as its escape under `%s` and `{}`, and as the
escape of its `int()` value under `%d`. -/
def stringArgRendering : Prop :=
  ∀ (s : String) (c : Conversion) (m : Markup), (FormatArg.ofString s).render c = .ok m →
    (c ≠ .percentInt → m = escape s) ∧
    (c = .percentInt → ∃ i, parsePyInt s = some i ∧ m = escape (toString i))

/-- `format_strings`: formatting any template with string arguments
replaces each field by `escape` of the string it refers to, and changes
nothing else. -/
def formatStrings : Prop :=
  ∀ (t : Markup) (ss : List String) (kv : List (String × String)) (r : Markup),
    t.formatWith (ss.map .ofString) (kv.map fun p => (p.1, .ofString p.2)) = .ok r →
    ∃ segs args, (∀ s ∈ segs, BraceSeg s) ∧ printSegs segs = t.str.toList ∧
      args.length = fieldCount segs ∧
      Forall₂ (fun rc s => rc.1.lookupStr ss kv = some s) (fieldRefs segs) args ∧
      r.str = String.ofList (fillSegs segs (args.map escape))

end Spec

end LeanMarkupsafe
