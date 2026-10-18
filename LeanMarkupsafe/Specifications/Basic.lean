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
  "amp;ltg#349".contains c

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

/-- `format` of an escaped template with safe arguments is escaped. -/
def formatClosed : Prop :=
  ∀ (t : Markup) (pos : List FormatArg) (named : List (String × FormatArg)) (r : Markup),
    IsEscaped t.str → (∀ a ∈ pos, a.Safe) → (∀ p ∈ named, p.2.Safe) →
    t.format pos named = .ok r → IsEscaped r.str

/-- `%` of an escaped template with safe arguments is escaped. -/
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

end Spec

end LeanMarkupsafe
