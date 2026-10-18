import LeanMarkupsafe.DataTypes.Basic
import LeanMarkupsafe.RepoImpl.Cursor

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

/-! ### The executable escape

`escape` is stated on `List Char`, where the proofs are; run as written it
would cost a stack frame and about 90 bytes per input character.
`escapeFast` escapes in one `String.foldl` into a `String`, and
`escape_eq_fast` (`@[csimp]`) makes every compiled `escape` run it. -/

/-- Append the escape of one character. -/
def escPush (acc : String) (c : Char) : String :=
  match c with
  | '&' => acc ++ "&amp;"
  | '<' => acc ++ "&lt;"
  | '>' => acc ++ "&gt;"
  | '"' => acc ++ "&#34;"
  | '\'' => acc ++ "&#39;"
  | c => acc.push c

/-- `escape`, in one pass into a `String`. -/
def escapeFast (s : String) : Markup := ⟨s.foldl escPush ""⟩

theorem escPush_toList (acc : String) (c : Char) :
    (escPush acc c).toList = acc.toList ++ escapeChar c := by
  unfold escPush escapeChar
  split <;> simp_all [String.toList_push]

theorem foldl_escPush (l : List Char) (acc : String) :
    (l.foldl escPush acc).toList = acc.toList ++ escapeList l := by
  induction l generalizing acc with
  | nil => simp [escapeList]
  | cons c cs ih => rw [List.foldl_cons, ih, escPush_toList]; simp [escapeList]

/-- The executable escape is `escape`. -/
@[csimp] theorem escape_eq_fast : @escape = @escapeFast := by
  funext s
  unfold escape escapeFast
  congr 1
  apply String.ext
  rw [String.foldl_eq_foldl_toList, foldl_escPush, String.toList_ofList]
  simp

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

/-- `Option` follows Python's `None`: `none` renders as `None` (upstream
`escape(None)`); use `escapeSilent` for the empty string. -/
instance {α : Type u} [ToMarkup α] : ToMarkup (Option α) where
  toMarkup
    | none => escape "None"
    | some x => ToMarkup.toMarkup x

/-- Python's bare `None`: `Markup.escape none` and `escapeSilent none` need no
type annotation, as in upstream (`escape(None)`). -/
@[default_instance low] instance noneToMarkup : ToMarkup (Option Empty) := ⟨fun _ => escape "None"⟩

instance : ToMarkup SoftString where
  toMarkup
    | .plain s => escape s
    | .markup m => m

namespace Markup

/-- Upstream `Markup.escape(obj)` / `escape(obj)` for any object: escapes
strings, keeps `Markup` and other `HasHtml` values as they render. -/
def escape {α : Type u} [ToMarkup α] (x : α) : Markup := ToMarkup.toMarkup x

/-- Upstream `Markup(obj)`: how a value is marked safe without escaping. -/
class ToMarkupSafe (α : Type u) where
  /-- Mark the value safe (upstream `Markup(obj)`). -/
  markSafe : α → Markup

instance : ToMarkupSafe String := ⟨Markup.mk⟩
instance {α : Type u} [HasHtml α] : ToMarkupSafe α := ⟨HasHtml.html⟩
instance (priority := low) {α : Type u} [ToString α] : ToMarkupSafe α := ⟨fun x => ⟨toString x⟩⟩

/-- Upstream `Markup(obj)`: a string marked safe as it is, an object with
`__html__` as its rendering, anything else as its `toString`, all unescaped:
`Markup.of "<em>hi</em>"`, `Markup.of 42`, `Markup.of img`. -/
def of {α : Type u} [ToMarkupSafe α] (x : α) : Markup := ToMarkupSafe.markSafe x

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

/-- `joinMarkup`, as one left fold into a `String` (constant stack). -/
def joinMarkupFast (sep : Markup) : List Markup → Markup
  | [] => empty
  | m :: ms => ⟨ms.foldl (fun acc x => acc ++ sep.str ++ x.str) m.str⟩

theorem foldl_join (sep : Markup) (x : Markup) (xs : List Markup) (a : String) :
    (x :: xs).foldl (fun acc x => acc ++ sep.str ++ x.str) a =
      a ++ sep.str ++ (joinMarkup sep (x :: xs)).str := by
  induction xs generalizing x a with
  | nil => simp [joinMarkup]
  | cons y ys ih =>
    rw [List.foldl_cons, ih]
    simp [joinMarkup, String.append_assoc]

/-- The executable `joinMarkup` is `joinMarkup`. -/
@[csimp] theorem joinMarkup_eq_fast : @joinMarkup = @joinMarkupFast := by
  funext sep ms
  cases ms with
  | nil => rfl
  | cons m ms =>
    cases ms with
    | nil => rfl
    | cons x xs =>
      show _ = Markup.mk _
      rw [foldl_join]
      cases m; simp [joinMarkup]; rfl

/-- Join the items with `sep` between them, escaping every item that is not
already markup (upstream `Markup.join`). -/
def join {α : Type u} [ToMarkup α] (sep : Markup) (xs : List α) : Markup :=
  joinMarkup sep (xs.map Markup.escape)

/-- `n` copies of `m` (upstream `Markup.__mul__`). -/
def times (m : Markup) : Nat → Markup
  | 0 => empty
  | n + 1 => m ++ times m n

/-- Append `n` copies of `m` to `acc` (constant stack). -/
def timesGo (m : Markup) : Nat → String → String
  | 0, acc => acc
  | n + 1, acc => timesGo m n (acc ++ m.str)

/-- `times`, as a loop into a `String`. -/
def timesFast (m : Markup) (n : Nat) : Markup := ⟨timesGo m n ""⟩

theorem timesGo_eq (m : Markup) (n : Nat) (acc : String) :
    timesGo m n acc = acc ++ (times m n).str := by
  induction n generalizing acc with
  | zero => simp [timesGo, times]
  | succ n ih => simp [timesGo, times, ih, String.append_assoc]

/-- The executable `times` is `times`. -/
@[csimp] theorem times_eq_fast : @times = @timesFast := by
  funext m n
  show times m n = ⟨timesGo m n ""⟩
  rw [timesGo_eq]; simp

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
