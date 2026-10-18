import LeanMarkupsafe.DataTypes.Basic

/-!
# Escaping

`escape` replaces `&`, `<`, `>`, `"` and `'` with `&amp;`, `&lt;`, `&gt;`,
`&#34;` and `&#39;`, exactly as upstream (`_native._escape_inner`, whose
chained `str.replace` calls amount to one substitution per character because
`&` is replaced first). The work is done on `List Char`, where the proofs are.

Also here: the generic `Markup.escape` (upstream `escape(obj)`, dispatching on
`HasHtml`), `escapeSilent`, `softStr`, concatenation that escapes the plain
side, `join` and repetition.
-/

namespace LeanMarkupsafe

/-- The replacement for one character. -/
def escapeChar : Char → List Char
  | '&' => ['&', 'a', 'm', 'p', ';']
  | '<' => ['&', 'l', 't', ';']
  | '>' => ['&', 'g', 't', ';']
  | '"' => ['&', '#', '3', '4', ';']
  | '\'' => ['&', '#', '3', '9', ';']
  | c => [c]

/-- `escape` on a character list. -/
def escapeList : List Char → List Char
  | [] => []
  | c :: l => escapeChar c ++ escapeList l

/-- Escape a string for HTML (upstream `escape(s)` for `s : str`). The result
satisfies `IsEscaped` (`escape_sound`) and `unescape` inverts it
(`unescape_escape`). -/
def escape (s : String) : Markup := ⟨String.ofList (escapeList s.toList)⟩

/-- How a value of type `α` becomes `Markup` under upstream's `escape(obj)`:
a string is escaped, a `HasHtml` value uses its own rendering, anything else
is converted with `toString` and escaped. -/
class ToMarkup (α : Type u) where
  /-- Upstream `escape(obj)`. -/
  toMarkup : α → Markup

instance : ToMarkup String := ⟨escape⟩

/-- A `HasHtml` value renders as its own HTML, unescaped (upstream checks
`__html__` before falling back to `str`). -/
instance (priority := default) instToMarkupOfHasHtml {α : Type u} [HasHtml α] : ToMarkup α :=
  ⟨HasHtml.html⟩

/-- Fallback: convert with `toString`, then escape (upstream `str(obj)`). -/
instance (priority := low) instToMarkupOfToString {α : Type u} [ToString α] : ToMarkup α :=
  ⟨fun x => escape (toString x)⟩

instance : ToMarkup SoftString where
  toMarkup
    | .plain s => escape s
    | .markup m => m

namespace Markup

/-- Upstream `Markup.escape(obj)` / `escape(obj)` for any object: escapes
strings, keeps `Markup` and other `HasHtml` values as they render. -/
def escape {α : Type u} [ToMarkup α] (x : α) : Markup := ToMarkup.toMarkup x

/-- Upstream `Markup(obj)` for an object with `__html__`: its rendering,
marked safe. -/
def ofHtml {α : Type u} [HasHtml α] (x : α) : Markup := HasHtml.html x

/-- Concatenate, escaping the right-hand side if it is not already markup
(upstream `Markup.__add__`). -/
def concat {α : Type u} [ToMarkup α] (m : Markup) (x : α) : Markup :=
  m ++ Markup.escape x

/-- Concatenate, escaping the left-hand side if it is not already markup
(upstream `Markup.__radd__`). -/
def rconcat {α : Type u} [ToMarkup α] (x : α) (m : Markup) : Markup :=
  Markup.escape x ++ m

instance : HAppend Markup String Markup := ⟨fun m s => m ++ LeanMarkupsafe.escape s⟩
instance : HAppend String Markup Markup := ⟨fun s m => LeanMarkupsafe.escape s ++ m⟩

/-- `sep` between the items, all already markup. -/
def joinMarkup (sep : Markup) : List Markup → Markup
  | [] => empty
  | [m] => m
  | m :: ms => m ++ sep ++ joinMarkup sep ms

/-- Join the items with `sep` between them, escaping every item that is not
already markup (upstream `Markup.join`). -/
def join {α : Type u} [ToMarkup α] (sep : Markup) (xs : List α) : Markup :=
  joinMarkup sep (xs.map Markup.escape)

/-- `n` copies of `m` (upstream `Markup.__mul__`). -/
def times (m : Markup) : Nat → Markup
  | 0 => empty
  | n + 1 => m ++ times m n

end Markup

/-- Like `Markup.escape`, but `none` is the empty markup (upstream
`escape_silent`, where `None` would otherwise render as `'None'`). -/
def escapeSilent {α : Type u} [ToMarkup α] : Option α → Markup
  | none => Markup.empty
  | some x => Markup.escape x

/-- How a value of type `α` behaves under upstream `soft_str`. -/
class ToSoftString (α : Type u) where
  /-- Upstream `soft_str(obj)`. -/
  soft : α → SoftString

instance : ToSoftString String := ⟨.plain⟩
instance : ToSoftString Markup := ⟨.markup⟩
instance : ToSoftString SoftString := ⟨id⟩
instance (priority := low) {α : Type u} [ToString α] : ToSoftString α :=
  ⟨fun x => .plain (toString x)⟩

/-- Convert to a string unless it already is one, keeping `Markup` as markup
so it will not be escaped again (upstream `soft_str`). -/
def softStr {α : Type u} [ToSoftString α] (x : α) : SoftString := ToSoftString.soft x

end LeanMarkupsafe
