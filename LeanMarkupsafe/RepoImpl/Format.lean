import LeanMarkupsafe.RepoImpl.Escape
import LeanMarkupsafe.RepoImpl.Unescape
import LeanMarkupsafe.RepoImpl.StripTags

/-!
# Interpolation: `Markup.format` and `Markup.mod`

Upstream `Markup.format` runs `str.format` with a formatter that escapes every
field, and `Markup.__mod__` runs `%` with every argument wrapped so that
`%s` escapes it. Here a `FormatArg` carries its own (already safe) rendering
under each `Conversion`, and the two template engines copy literal text and
insert the renderings.

Supported `str.format` syntax: literal text, `{{` and `}}`, and fields
`{}`, `{0}`, `{name}`, each with an optional `:spec` handed to the argument.
Supported `%` syntax: `%%`, `%s`, `%d`, `%i`, and `%(key)s`/`%(key)d`/
`%(key)i`. Attribute and index access in fields (`{0.x}`, `{0[1]}`),
`!r`-style conversions, nested specs and `%` flags, widths and precisions
are rejected with `FormatError.unsupported` (deviations recorded in
`docs/traceability.toml`).
-/

namespace LeanMarkupsafe

/-- Digits with single `_` separators between them (Python's integer
literal grammar for base 10): the digit list, if well formed. -/
def pyDigits : List Char → Option (List Char)
  | [] => none
  | [c] => if isDecDigit c then some [c] else none
  | c :: d :: l =>
    if isDecDigit c then
      if d = '_' then
        match l with
        | e :: _ => if isDecDigit e then (pyDigits l).map (c :: ·) else none
        | [] => none
      else (pyDigits (d :: l)).map (c :: ·)
    else none

/-- `pyDigits` with an accumulator (the digits so far, reversed): constant
stack. -/
def pyDigitsGo : List Char → List Char → Option (List Char)
  | [], _ => none
  | [c], acc => if isDecDigit c then some (c :: acc).reverse else none
  | c :: d :: l, acc =>
    if isDecDigit c then
      if d = '_' then
        match l with
        | e :: _ => if isDecDigit e then pyDigitsGo l (c :: acc) else none
        | [] => none
      else pyDigitsGo (d :: l) (c :: acc)
    else none

theorem pyDigitsGo_eq (l acc : List Char) :
    pyDigitsGo l acc = (pyDigits l).map (acc.reverse ++ ·) := by
  induction l using pyDigits.induct generalizing acc <;> simp_all [pyDigitsGo, pyDigits] <;> rfl

/-- `pyDigits`, with constant stack. -/
def pyDigitsFast (l : List Char) : Option (List Char) := pyDigitsGo l []

/-- The executable `pyDigits` is `pyDigits`. -/
@[csimp] theorem pyDigits_eq_fast : @pyDigits = @pyDigitsFast := by
  funext l; rw [pyDigitsFast, pyDigitsGo_eq]; simp

/-- Python's `int(s)` grammar for a string: surrounding whitespace stripped,
an optional sign, ASCII decimal digits with single underscores between them.
The sign (`true` for `-`) and the digits, if well formed. (Python also
accepts non-ASCII decimal digits; this port does not.) -/
def pyIntLiteral (s : String) : Option (Bool × List Char) :=
  let l := (s.toList.dropWhile isPySpace).reverse.dropWhile isPySpace |>.reverse
  match l with
  | '-' :: r => (pyDigits r).map (true, ·)
  | '+' :: r => (pyDigits r).map (false, ·)
  | r => (pyDigits r).map (false, ·)

/-! ### `int()` literals in one pass

`pyIntLiteral` strips the string through `List Char`. `intStep` is the same
grammar as a six-state machine folded over the string in place;
`pyIntLiteral_eq_fast` proves the fold equal, and `percentIntOfText` counts
the digits with the same fold before it builds anything, so a literal over
the limit is rejected after one scan. -/

theorem digit_not_space {x : Char} (h : isDecDigit x = true) : isPySpace x = false := by
  unfold isDecDigit at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : 48 ≤ x.toNat := h.1
  have h2 : x.toNat ≤ 57 := h.2
  unfold isPySpace
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne]
  omega

/-- Strip trailing Python whitespace. -/
def rstripPy (l : List Char) : List Char := (l.reverse.dropWhile isPySpace).reverse

theorem rstripPy_nil : rstripPy [] = [] := rfl

theorem rstripPy_cons (y : Char) (t : List Char) :
    rstripPy (y :: t) = if rstripPy t = [] ∧ isPySpace y = true then [] else y :: rstripPy t := by
  unfold rstripPy
  rw [List.reverse_cons, List.dropWhile_append]
  by_cases h : (t.reverse.dropWhile isPySpace).isEmpty = true
  · have h' : t.reverse.dropWhile isPySpace = [] := List.isEmpty_iff.mp h
    rw [ite_eq_left h, h']
    by_cases hy : isPySpace y = true <;> simp [hy, List.dropWhile]
  · rw [ite_eq_right h]
    have hne : (t.reverse.dropWhile isPySpace).reverse ≠ [] := by simpa [List.isEmpty_iff] using h
    simp [hne]

theorem rstripPy_cons_of_not {y : Char} (t : List Char) (h : isPySpace y = false) :
    rstripPy (y :: t) = y :: rstripPy t := by
  rw [rstripPy_cons]; simp [h]

/-- Trailing whitespace only: accepted, with no more digits. -/
def intRunT : List Char → Option (List Char)
  | [] => some []
  | x :: t => if isPySpace x then intRunT t else none

/-- After a digit: the digits still to come, if the rest is well formed. -/
def intRunD : List Char → Option (List Char)
  | [] => some []
  | x :: t =>
    if isDecDigit x then (intRunD t).map (x :: ·)
    else if x = '_' then
      match t with
      | y :: t' => if isDecDigit y then (intRunD t').map (y :: ·) else none
      | [] => none
    else if isPySpace x then intRunT t
    else none

theorem intRunD_cons (x : Char) (t : List Char) :
    intRunD (x :: t) =
      if isDecDigit x then (intRunD t).map (x :: ·)
      else if x = '_' then
        match t with
        | y :: t' => if isDecDigit y then (intRunD t').map (y :: ·) else none
        | [] => none
      else if isPySpace x then intRunT t
      else none := by
  cases t <;> rfl

/-- After a sign: a digit must come. -/
def intRunS : List Char → Option (List Char)
  | x :: t => if isDecDigit x then (intRunD t).map (x :: ·) else none
  | [] => none

/-- `pyIntLiteral` on a character list, left to right. -/
def intRunL : List Char → Option (Bool × List Char)
  | [] => none
  | x :: t =>
    if isPySpace x then intRunL t
    else if x = '-' then (intRunS t).map (true, ·)
    else if x = '+' then (intRunS t).map (false, ·)
    else if isDecDigit x then (intRunD t).map fun d => (false, x :: d)
    else none

theorem intRunT_eq (t : List Char) : intRunT t = if rstripPy t = [] then some [] else none := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    rw [intRunT, rstripPy_cons]
    by_cases hx : isPySpace x = true
    · rw [ite_eq_left hx, ih]; by_cases hr : rstripPy t = [] <;> simp [hr, hx]
    · simp [hx]

theorem pyDigits_cons_nondigit {x : Char} (R : List Char) (h : isDecDigit x = false) :
    pyDigits (x :: R) = none := by
  cases R <;> simp [pyDigits, h]

theorem pyDigits_rstrip (n : Nat) : ∀ (t : List Char) (c : Char), t.length ≤ n →
    isDecDigit c = true → pyDigits (c :: rstripPy t) = (intRunD t).map (c :: ·) := by
  induction n with
  | zero =>
    intro t c ht hc
    cases t with
    | nil => simp [rstripPy_nil, pyDigits, hc, intRunD]
    | cons => simp at ht
  | succ n ih =>
    intro t c ht hc
    cases t with
    | nil => simp [rstripPy_nil, pyDigits, hc, intRunD]
    | cons x t =>
      simp only [List.length_cons] at ht
      rw [intRunD_cons]
      by_cases hx : isDecDigit x = true
      · rw [rstripPy_cons_of_not t (digit_not_space hx), ite_eq_left hx]
        have hne : x ≠ '_' := by rintro rfl; simp [isDecDigit] at hx
        simp only [pyDigits, hc, ite_true, hne, ite_false]
        rw [ih t x (by omega) hx]
      · rw [ite_eq_right hx]
        by_cases hu : x = '_'
        · subst hu
          rw [rstripPy_cons_of_not t (by decide), ite_eq_left rfl]
          simp only [pyDigits, hc, ite_true]
          cases t with
          | nil => simp [rstripPy_nil]
          | cons y t' =>
            simp only [List.length_cons] at ht
            by_cases hy : isDecDigit y = true
            · rw [rstripPy_cons_of_not t' (digit_not_space hy)]
              simp only [hy, ite_true]
              rw [ih t' y (by omega) hy]
            · rw [rstripPy_cons]
              have hy' : isDecDigit y = false := by simpa using hy
              by_cases hr : rstripPy t' = [] ∧ isPySpace y = true
              · rw [ite_eq_left hr]; simp [hy']
              · rw [ite_eq_right hr]; simp [hy']
        · rw [ite_eq_right hu]
          have hx' : isDecDigit x = false := by simpa using hx
          by_cases hs : isPySpace x = true
          · rw [ite_eq_left hs, intRunT_eq, rstripPy_cons]
            by_cases hr : rstripPy t = []
            · simp [hr, hs, pyDigits, hc]
            · simp only [hr, false_and, ite_false]
              simp [pyDigits, hc, hu, pyDigits_cons_nondigit _ hx']
          · rw [ite_eq_right hs, rstripPy_cons_of_not t (by simpa using hs)]
            simp [pyDigits, hc, hu, pyDigits_cons_nondigit _ hx']

theorem intRunS_eq (t : List Char) : intRunS t = pyDigits (rstripPy t) := by
  cases t with
  | nil => rfl
  | cons x t =>
    rw [intRunS]
    by_cases hx : isDecDigit x = true
    · rw [ite_eq_left hx, rstripPy_cons_of_not t (digit_not_space hx),
        pyDigits_rstrip _ t x (Nat.le_refl _) hx]
    · have hx' : isDecDigit x = false := by simpa using hx
      rw [ite_eq_right hx, rstripPy_cons]
      split
      · rfl
      · rw [pyDigits_cons_nondigit _ hx']

theorem intRunL_eq (l : List Char) :
    intRunL l = match rstripPy (l.dropWhile isPySpace) with
      | '-' :: r => (pyDigits r).map (true, ·)
      | '+' :: r => (pyDigits r).map (false, ·)
      | r => (pyDigits r).map (false, ·) := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [intRunL]
    by_cases hs : isPySpace x = true
    · rw [ite_eq_left hs, ih, List.dropWhile_cons_of_pos hs]
    · have hs' : isPySpace x = false := by simpa using hs
      rw [ite_eq_right hs, List.dropWhile_cons_of_neg hs, rstripPy_cons_of_not t hs']
      by_cases hm : x = '-'
      · subst hm; simp [intRunS_eq]
      · by_cases hp : x = '+'
        · subst hp; simp [intRunS_eq]
        · rw [ite_eq_right hm, ite_eq_right hp]
          have key : (match x :: rstripPy t with
              | '-' :: r => (pyDigits r).map (true, ·)
              | '+' :: r => (pyDigits r).map (false, ·)
              | r => (pyDigits r).map (false, ·)) = (pyDigits (x :: rstripPy t)).map (false, ·) := by
            split
            · rename_i r h; simp at h; exact absurd h.1 hm
            · rename_i r h; simp at h; exact absurd h.1 hp
            · rfl
          rw [key]
          by_cases hd : isDecDigit x = true
          · rw [ite_eq_left hd, pyDigits_rstrip _ t x (Nat.le_refl _) hd]
            cases intRunD t <;> rfl
          · rw [ite_eq_right hd, pyDigits_cons_nondigit _ (by simpa using hd)]; rfl

theorem pyIntLiteral_eq_run (s : String) : pyIntLiteral s = intRunL s.toList := by
  rw [intRunL_eq]; rfl

/-- Where the literal grammar stands after a prefix of the string. -/
inductive IntPhase where
  | lead | sign | digit | under | trail | bad
  deriving DecidableEq

/-- One character of the grammar: the phase, the sign, and what `emit` has
made of the digits so far. -/
def intStep {β : Type} (emit : β → Char → β) (st : IntPhase × Bool × β) (c : Char) :
    IntPhase × Bool × β :=
  match st.1 with
  | .lead =>
    if isPySpace c then st
    else if c = '-' then (.sign, true, st.2.2)
    else if c = '+' then (.sign, false, st.2.2)
    else if isDecDigit c then (.digit, false, emit st.2.2 c)
    else (.bad, st.2)
  | .sign => if isDecDigit c then (.digit, st.2.1, emit st.2.2 c) else (.bad, st.2)
  | .digit =>
    if isDecDigit c then (.digit, st.2.1, emit st.2.2 c)
    else if c = '_' then (.under, st.2)
    else if isPySpace c then (.trail, st.2)
    else (.bad, st.2)
  | .under => if isDecDigit c then (.digit, st.2.1, emit st.2.2 c) else (.bad, st.2)
  | .trail => if isPySpace c then st else (.bad, st.2)
  | .bad => st

/-- The sign and the digits' image, if the string ended in an accepting
phase. -/
def intFinish {β : Type} (st : IntPhase × Bool × β) : Option (Bool × β) :=
  match st.1 with
  | .digit | .trail => some st.2
  | _ => none

section
variable {β : Type} (emit : β → Char → β)

theorem fold_bad (t : List Char) (neg : Bool) (b : β) :
    intFinish (t.foldl (intStep emit) (.bad, neg, b)) = none := by
  induction t with
  | nil => rfl
  | cons x t ih => simp only [List.foldl_cons, intStep]; exact ih

theorem fold_trail (t : List Char) (neg : Bool) (b : β) :
    intFinish (t.foldl (intStep emit) (.trail, neg, b)) =
      (intRunT t).map fun e => (neg, e.foldl emit b) := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    simp only [List.foldl_cons, intStep, intRunT]
    by_cases hx : isPySpace x = true
    · simp only [hx, ite_true]; exact ih
    · simp only [hx, Bool.false_eq_true, ite_false]; exact fold_bad emit t neg b

theorem fold_digit (t : List Char) :
    (∀ neg b, intFinish (t.foldl (intStep emit) (.digit, neg, b)) =
      (intRunD t).map fun e => (neg, e.foldl emit b)) ∧
    (∀ neg b, intFinish (t.foldl (intStep emit) (.under, neg, b)) =
      (match t with
       | y :: t' => if isDecDigit y then (intRunD t').map (y :: ·) else none
       | [] => none).map fun (e : List Char) => (neg, e.foldl emit b)) := by
  induction t with
  | nil => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | cons x t ih =>
    refine ⟨fun neg b => ?_, fun neg b => ?_⟩
    · simp only [List.foldl_cons, intStep, intRunD_cons]
      by_cases hd : isDecDigit x = true
      · simp only [hd, ite_true]; rw [ih.1]; cases intRunD t <;> rfl
      · simp only [hd, Bool.false_eq_true, ite_false]
        by_cases hu : x = '_'
        · simp only [hu, ite_true]; exact ih.2 neg b
        · simp only [hu, ite_false]
          by_cases hs : isPySpace x = true
          · simp only [hs, ite_true]; exact fold_trail emit t neg b
          · simp only [hs, Bool.false_eq_true, ite_false]; exact fold_bad emit t neg b
    · simp only [List.foldl_cons, intStep]
      by_cases hd : isDecDigit x = true
      · simp only [hd, ite_true]; rw [ih.1]; cases intRunD t <;> rfl
      · simp only [hd, Bool.false_eq_true, ite_false]; exact fold_bad emit t neg b

theorem fold_lead (l : List Char) (neg : Bool) (b : β) :
    intFinish (l.foldl (intStep emit) (.lead, neg, b)) =
      (intRunL l).map fun p => (p.1, p.2.foldl emit b) := by
  induction l generalizing neg with
  | nil => rfl
  | cons x t ih =>
    simp only [List.foldl_cons, intStep, intRunL]
    have sign : ∀ n, intFinish (t.foldl (intStep emit) (.sign, n, b)) =
        ((intRunS t).map (n, ·)).map fun p => (p.1, p.2.foldl emit b) := by
      intro n
      cases t with
      | nil => rfl
      | cons y t' =>
        simp only [List.foldl_cons, intStep, intRunS]
        by_cases hy : isDecDigit y = true
        · simp only [hy, ite_true]; rw [(fold_digit emit t').1]; cases intRunD t' <;> rfl
        · simp only [hy, Bool.false_eq_true, ite_false]; exact fold_bad emit t' n b
    by_cases hs : isPySpace x = true
    · simp only [hs, ite_true]; exact ih neg
    · simp only [hs, Bool.false_eq_true, ite_false]
      by_cases hm : x = '-'
      · simp only [hm, ite_true]; exact sign true
      · simp only [hm, ite_false]
        by_cases hp : x = '+'
        · simp only [hp, ite_true]; exact sign false
        · simp only [hp, ite_false]
          by_cases hd : isDecDigit x = true
          · simp only [hd, ite_true]; rw [(fold_digit emit t).1]; cases intRunD t <;> rfl
          · simp only [hd, Bool.false_eq_true, ite_false]; exact fold_bad emit t neg b

end

/-- `pyIntLiteral`, in one fold over the string. -/
def pyIntLiteralFast (s : String) : Option (Bool × List Char) :=
  (intFinish (s.foldl (intStep fun l c => c :: l) (.lead, false, []))).map fun p => (p.1, p.2.reverse)

/-- The executable `pyIntLiteral` is `pyIntLiteral`. -/
@[csimp] theorem pyIntLiteral_eq_fast : @pyIntLiteral = @pyIntLiteralFast := by
  funext s
  rw [pyIntLiteralFast, String.foldl_eq_foldl_toList, fold_lead, pyIntLiteral_eq_run]
  cases intRunL s.toList <;> simp

/-- The sign and the number of digits of the literal, in one fold. -/
def pyIntDigitCount (s : String) : Option (Bool × Nat) :=
  intFinish (s.foldl (intStep fun n _ => n + 1) (.lead, false, 0))

theorem pyIntDigitCount_eq (s : String) :
    pyIntDigitCount s = (pyIntLiteral s).map fun p => (p.1, p.2.length) := by
  rw [pyIntDigitCount, String.foldl_eq_foldl_toList, fold_lead, pyIntLiteral_eq_run]
  cases intRunL s.toList <;> simp

/-- The integer a sign and digit list stand for. -/
def pyIntValue (neg : Bool) (d : List Char) : Int :=
  if neg then -(decValue d : Int) else (decValue d : Int)

/-- Python `int(s)` for a string (see `pyIntLiteral`). -/
def parsePyInt (s : String) : Option Int :=
  (pyIntLiteral s).map fun p => pyIntValue p.1 p.2

/-- CPython's default limit on the digits `int()` converts from a string
(`sys.get_int_max_str_digits()`); a longer literal is a `ValueError`. -/
def intMaxStrDigits : Nat := 4300

/-- CPython's error for an `int()` literal over the digit limit. -/
def intLimitError (n : Nat) : FormatError :=
  .typeError s!"Exceeds the limit ({intMaxStrDigits} digits) for integer string conversion: value has {n} digits; use sys.set_int_max_str_digits() to increase the limit"

/-- CPython's error for a malformed `int()` literal. -/
def invalidIntError (s : String) : FormatError :=
  .typeError s!"invalid literal for int() with base 10: '{s}'"

/-- `%d` of a text value: upstream converts the argument with `int()`, which
rejects a malformed literal and one of more than 4300 digits. -/
def percentIntOfText (s : String) : Except FormatError Markup :=
  match pyIntLiteral s with
  | some (neg, d) =>
    if intMaxStrDigits < d.length then .error (intLimitError d.length)
    else .ok (escape (toString (pyIntValue neg d)))
  | none => .error (invalidIntError s)

/-- `percentIntOfText`, counting the digits in one pass first, so a literal
over the limit is rejected before any digit is stored. -/
def percentIntOfTextFast (s : String) : Except FormatError Markup :=
  match pyIntDigitCount s with
  | none => .error (invalidIntError s)
  | some (_, n) => if intMaxStrDigits < n then .error (intLimitError n) else percentIntOfText s

/-- The executable `percentIntOfText` is `percentIntOfText`. -/
@[csimp] theorem percentIntOfText_eq_fast : @percentIntOfText = @percentIntOfTextFast := by
  funext s
  unfold percentIntOfTextFast
  rw [pyIntDigitCount_eq]
  cases h : pyIntLiteral s with
  | none => simp [percentIntOfText, h]
  | some p =>
    obtain ⟨neg, d⟩ := p
    simp only [Option.map_some]
    by_cases hl : intMaxStrDigits < d.length
    · simp [percentIntOfText, h, hl]
    · simp [hl]

namespace FormatArg

/-- A string argument: escaped under `%s` and `{}`; under `%d` it is parsed
as Python `int()` does and the integer is rendered. -/
def ofString (s : String) : FormatArg where
  render
    | .percentStr => .ok (escape s)
    | .percentInt => percentIntOfText s
    | .brace spec =>
      if spec.isEmpty then .ok (escape s)
      else .error (.unsupported s!"format spec '{spec}' for a string")

/-- An integer argument: its decimal text under every conversion. -/
def ofInt (i : Int) : FormatArg where
  render
    | .percentStr => .ok (escape (toString i))
    | .percentInt => .ok (escape (toString i))
    | .brace spec =>
      if spec.isEmpty then .ok (escape (toString i))
      else .error (.unsupported s!"format spec '{spec}' for an integer")

/-- A natural-number argument, as `ofInt`. -/
def ofNat (n : Nat) : FormatArg := ofInt n

/-- A `HasHtml` argument: its HTML rendering, unescaped; a format spec is an
error, as upstream raises when a class defines `__html__` but not
`__html_format__`. -/
def ofHtml {α : Type u} [HasHtml α] (x : α) : FormatArg where
  render
    | .percentStr => .ok (HasHtml.html x)
    | .percentInt => .error (.typeError "%d format: a real number is required")
    | .brace spec =>
      if spec.isEmpty then .ok (HasHtml.html x)
      else .error (.unsupportedSpec s!"Format specifier {spec} given, but the value does not define __html_format__. A class that defines __html__ must define __html_format__ to work with format specifiers.")

/-- A `Markup` argument: inserted verbatim; `%d` parses its text with
`int()`; a format spec is an error (upstream `Markup.__html_format__`). -/
def ofMarkup (m : Markup) : FormatArg where
  render
    | .percentStr => .ok m
    | .percentInt => percentIntOfText m.str
    | .brace spec =>
      if spec.isEmpty then .ok m
      else .error (.unsupportedSpec "Unsupported format specification for Markup.")

/-- A `HasHtmlFormat` argument: every brace field goes through
`htmlFormat` with its spec (upstream `__html_format__`). -/
def ofHtmlFormat {α : Type u} [HasHtmlFormat α] (x : α) : FormatArg where
  render
    | .percentStr => .ok (HasHtml.html x)
    | .percentInt => .error (.typeError "%d format: a real number is required")
    | .brace spec => HasHtmlFormat.htmlFormat x spec

end FormatArg

/-- A string literal can stand for a string argument:
`t.format [("name", "World")]`. -/
instance : Coe String FormatArg := ⟨FormatArg.ofString⟩
instance : Coe Markup FormatArg := ⟨FormatArg.ofMarkup⟩
instance : Coe Int FormatArg := ⟨FormatArg.ofInt⟩
instance : Coe Nat FormatArg := ⟨FormatArg.ofNat⟩

/-- Values that can be passed to `format`/`%`. -/
class ToFormatArg (α : Type u) where
  toFormatArg : α → FormatArg

instance : ToFormatArg FormatArg := ⟨id⟩
instance : ToFormatArg String := ⟨FormatArg.ofString⟩
instance : ToFormatArg Markup := ⟨FormatArg.ofMarkup⟩
instance : ToFormatArg Int := ⟨FormatArg.ofInt⟩
instance : ToFormatArg Nat := ⟨FormatArg.ofNat⟩
instance (priority := 200) {α : Type u} [HasHtmlFormat α] : ToFormatArg α :=
  ⟨FormatArg.ofHtmlFormat⟩
instance (priority := low) {α : Type u} [HasHtml α] : ToFormatArg α := ⟨FormatArg.ofHtml⟩

/-- Map the success value, keep the error. -/
def mapOk (f : List Char → List Char) : Except FormatError (List Char) → Except FormatError (List Char)
  | .ok o => .ok (f o)
  | .error e => .error e

/-! ## `str.format` -/

/-- Field numbering state: no field yet, automatic (`{}`, next index), or
manual (`{0}`). Upstream rejects mixing the two. -/
inductive Numbering where
  | unset
  | auto (next : Nat)
  | manual
  deriving DecidableEq, Repr

/-- The contents of a field up to its closing `}`, and the rest after it. -/
def takeField : List Char → Except FormatError (List Char × List Char)
  | [] => .error (.badTemplate "expected '}' before end of string")
  | c :: l =>
    if c = '}' then .ok ([], l)
    else if c = '{' then .error (.unsupported "nested replacement fields in a format spec")
    else match takeField l with
      | .ok (f, r) => .ok (c :: f, r)
      | .error e => .error e

theorem takeField_spec {l f r : List Char} (h : takeField l = .ok (f, r)) :
    l = f ++ '}' :: r := by
  induction l generalizing f with
  | nil => simp [takeField] at h
  | cons c l ih =>
    unfold takeField at h
    split at h
    · cases h; simp_all
    · split at h
      · cases h
      · split at h
        · rename_i f' r' heq
          cases h; rw [ih heq]; rfl
        · cases h

theorem takeField_length {l f r : List Char} (h : takeField l = .ok (f, r)) :
    r.length < l.length := by
  rw [takeField_spec h]; simp; omega

/-- Split a field into its name and its spec (after the first `:`). -/
def splitField (field : List Char) : List Char × List Char :=
  let name := field.takeWhile (· ≠ ':')
  (name, (field.drop name.length).drop 1)

/-- What a field's name says: `{}` (next automatic index), `{0}` (an
explicit index) or `{name}` (a keyword). `%s` is `auto` and `%(key)s` is
`key`. -/
inductive FieldName where
  | auto
  | index (i : Nat)
  | key (k : String)
  deriving DecidableEq, Repr

/-- The argument a field draws on: a position or a keyword. -/
inductive ArgRef where
  | pos (i : Nat)
  | key (k : String)
  deriving DecidableEq, Repr

/-- The argument `r` refers to. -/
def ArgRef.lookup (pos : List FormatArg) (named : List (String × FormatArg)) :
    ArgRef → Option FormatArg
  | .pos i => pos[i]?
  | .key k => named.lookup k

/-- The reference a field name makes when `n` automatic fields precede it. -/
def FieldName.ref (n : Nat) : FieldName → ArgRef
  | .auto => .pos n
  | .index i => .pos i
  | .key k => .key k

/-- The automatic counter after a field. -/
def FieldName.next (n : Nat) : FieldName → Nat
  | .auto => n + 1
  | _ => n

/-- Read a field name. -/
def parseFieldName (name : List Char) : Except FormatError FieldName :=
  if name.any (fun c => c = '.' || c = '[' || c = '!') then
    .error (.unsupported "attribute, index or conversion in a format field")
  else if name.isEmpty then .ok .auto
  else if name.all isDecDigit then .ok (.index (decValue name))
  else .ok (.key (String.ofList name))

/-- The automatic counter a numbering state holds. -/
def Numbering.counter : Numbering → Nat
  | .auto n => n
  | _ => 0

/-- The numbering state after a field, or the mixing error. -/
def Numbering.step : Numbering → FieldName → Except FormatError Numbering
  | .manual, .auto => .error .mixedNumbering
  | st, .auto => .ok (.auto (st.counter + 1))
  | .auto _, .index _ => .error .mixedNumbering
  | _, .index _ => .ok .manual
  | st, .key _ => .ok st

/-- Look up the argument a field names, advancing the numbering. -/
def resolveField (pos : List FormatArg) (named : List (String × FormatArg))
    (st : Numbering) (name : List Char) : Except FormatError (FormatArg × Numbering) :=
  match parseFieldName name with
  | .error e => .error e
  | .ok fn =>
    match st.step fn with
    | .error e => .error e
    | .ok st' =>
      match (fn.ref st.counter).lookup pos named with
      | some a => .ok (a, st')
      | none =>
        match fn.ref st.counter with
        | .pos i => .error (.indexOutOfRange i)
        | .key k => .error (.missingKey k)

/-- Render one field. -/
def renderField (pos : List FormatArg) (named : List (String × FormatArg))
    (st : Numbering) (field : List Char) : Except FormatError (Markup × Numbering) :=
  let nf := splitField field
  match resolveField pos named st nf.1 with
  | .error e => .error e
  | .ok (a, st') =>
    match a.render (.brace (String.ofList nf.2)) with
    | .error e => .error e
    | .ok m => .ok (m, st')

/-- Keyword arguments as a hash map, built once per call. The first binding
of a key wins, as in `List.lookup` (the specification). -/
def namedMap (named : List (String × FormatArg)) : Std.HashMap String FormatArg :=
  named.foldl (fun m p => m.insertIfNew p.1 p.2) (Std.HashMap.emptyWithCapacity named.length)

theorem namedMap_fold (l : List (String × FormatArg)) (m : Std.HashMap String FormatArg) (a : String) :
    (l.foldl (fun m p => m.insertIfNew p.1 p.2) m)[a]? = (m[a]?).or (l.lookup a) := by
  induction l generalizing m with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih, Std.HashMap.getElem?_insertIfNew]
    simp only [List.lookup]
    by_cases hk : p.1 = a
    · subst hk
      by_cases hm : p.1 ∈ m <;> simp [hm]
    · have : (a == p.1) = false := by simp; exact fun h => hk h.symm
      simp [hk, this]

theorem namedMap_get (named : List (String × FormatArg)) (a : String) : (namedMap named)[a]? = named.lookup a := by
  rw [namedMap, namedMap_fold, Std.HashMap.getElem?_emptyWithCapacity]; simp

/-- A `%` mapping as a hash map, built once per call. A Python `dict` keeps
the last binding of a repeated key, so this inserts with `insert` and the
last binding wins, as `List.lookup` on the reversed list (the
specification, `dictMap_get`). -/
def dictMap (kv : List (String × FormatArg)) : Std.HashMap String FormatArg :=
  kv.foldl (fun m p => m.insert p.1 p.2) (Std.HashMap.emptyWithCapacity kv.length)

theorem dictMap_fold (l : List (String × FormatArg)) (m : Std.HashMap String FormatArg) (a : String) :
    (l.foldl (fun m p => m.insert p.1 p.2) m)[a]? = (l.reverse.lookup a).or (m[a]?) := by
  induction l generalizing m with
  | nil => simp
  | cons p l ih =>
    rw [List.foldl_cons, ih, Std.HashMap.getElem?_insert, List.reverse_cons, List.lookup_append]
    simp only [List.lookup]
    by_cases hk : p.1 = a
    · subst hk; simp
    · have : (a == p.1) = false := by simp; exact fun h => hk h.symm
      simp [hk, this]

theorem dictMap_get (kv : List (String × FormatArg)) (a : String) :
    (dictMap kv)[a]? = kv.reverse.lookup a := by
  rw [dictMap, dictMap_fold, Std.HashMap.getElem?_emptyWithCapacity]; simp

/-- `ArgRef.lookup` with the positional arguments in an `Array` and the
keyword arguments in a hash map: constant time per field. -/
def ArgRef.lookupA (pos : Array FormatArg) (named : Std.HashMap String FormatArg) :
    ArgRef → Option FormatArg
  | .pos i => pos[i]?
  | .key k => named[k]?

/-- `resolveField` with the positional arguments in an `Array`. -/
def resolveFieldA (pos : Array FormatArg) (named : Std.HashMap String FormatArg)
    (st : Numbering) (name : List Char) : Except FormatError (FormatArg × Numbering) :=
  match parseFieldName name with
  | .error e => .error e
  | .ok fn =>
    match st.step fn with
    | .error e => .error e
    | .ok st' =>
      match (fn.ref st.counter).lookupA pos named with
      | some a => .ok (a, st')
      | none =>
        match fn.ref st.counter with
        | .pos i => .error (.indexOutOfRange i)
        | .key k => .error (.missingKey k)

/-- `renderField` with the positional arguments in an `Array`. -/
def renderFieldA (pos : Array FormatArg) (named : Std.HashMap String FormatArg)
    (st : Numbering) (field : List Char) : Except FormatError (Markup × Numbering) :=
  let nf := splitField field
  match resolveFieldA pos named st nf.1 with
  | .error e => .error e
  | .ok (a, st') =>
    match a.render (.brace (String.ofList nf.2)) with
    | .error e => .error e
    | .ok m => .ok (m, st')

theorem ArgRef.lookupA_toArray (pos : List FormatArg) (named : List (String × FormatArg))
    (r : ArgRef) : r.lookupA pos.toArray (namedMap named) = r.lookup pos named := by
  cases r <;> simp [ArgRef.lookupA, ArgRef.lookup, namedMap_get]

theorem renderFieldA_toArray (pos : List FormatArg) (named : List (String × FormatArg))
    (st : Numbering) (field : List Char) :
    renderFieldA pos.toArray (namedMap named) st field = renderField pos named st field := by
  simp only [renderFieldA, renderField, resolveFieldA, resolveField, ArgRef.lookupA_toArray]

/-- The `str.format` engine on a character list. -/
def formatList (pos : List FormatArg) (named : List (String × FormatArg)) :
    Numbering → List Char → Except FormatError (List Char)
  | _, [] => .ok []
  | st, c :: l =>
    if c = '{' then
      if l.head? = some '{' then mapOk ('{' :: ·) (formatList pos named st l.tail)
      else
        match h : takeField l with
        | .error e => .error e
        | .ok (field, r) =>
          have : r.length < l.length + 1 := by have := takeField_length h; omega
          match renderField pos named st field with
          | .error e => .error e
          | .ok (m, st') => mapOk (m.str.toList ++ ·) (formatList pos named st' r)
    else if c = '}' then
      if l.head? = some '}' then mapOk ('}' :: ·) (formatList pos named st l.tail)
      else .error (.badTemplate "Single '}' encountered in format string")
    else mapOk (c :: ·) (formatList pos named st l)
termination_by _ l => l.length

/-- `str.format` on markup with positional and keyword arguments, escaping
every argument that is not already safe. `Markup.format` is the same with
the arguments written as upstream writes them. -/
def Markup.formatWith (t : Markup) (pos : List FormatArg)
    (named : List (String × FormatArg) := []) : Except FormatError Markup :=
  match formatList pos named .unset t.str.toList with
  | .ok o => .ok ⟨String.ofList o⟩
  | .error e => .error e

/-! ### The executable `str.format` engine

`formatList` recurses once per template character and builds a `List Char`.
`fmtGo` reads the template in place through a `Cursor` and appends each
literal character and each rendered field to a `String`, with constant
stack; `formatWith_eq_fast` (`@[csimp]`) proves it equal. -/

/-- A field after its `{`: its rendering, the numbering after it and the
text after its `}`. -/
def fieldL (pos : List FormatArg) (named : List (String × FormatArg)) (st : Numbering)
    (l : List Char) : Except FormatError (Markup × Numbering × List Char) :=
  match takeField l with
  | .error e => .error e
  | .ok (field, r) =>
    match renderField pos named st field with
    | .error e => .error e
    | .ok (m, st') => .ok (m, st', r)

theorem formatList_lbrace (pos : List FormatArg) (named : List (String × FormatArg))
    (st : Numbering) (l : List Char) :
    formatList pos named st ('{' :: l) =
      if l.head? = some '{' then mapOk ('{' :: ·) (formatList pos named st l.tail)
      else match fieldL pos named st l with
        | .error e => .error e
        | .ok (m, st', r) => mapOk (m.str.toList ++ ·) (formatList pos named st' r) := by
  rw [formatList]
  simp only [ite_true]
  split
  · rfl
  · unfold fieldL
    split
    · rename_i e h; simp [h]
    · rename_i field r h
      simp only [h]
      cases renderField pos named st field <;> rfl

theorem mapOk_ok (f : List Char → List Char) (o : List Char) : mapOk f (.ok o) = .ok (f o) := rfl
theorem mapOk_error (f : List Char → List Char) (e : FormatError) :
    mapOk f (.error e) = .error e := rfl

namespace Cursor

variable {s : String.Slice}

/-- `takeField`, in place: the field (its characters in `accRev`, reversed,
so far) and the position after its `}`. -/
def takeFieldAt (p : s.Pos) (accRev : List Char) : Except FormatError (List Char × s.Pos) :=
  if h : p = s.endPos then .error (.badTemplate "expected '}' before end of string")
  else if p.get h = '}' then .ok (accRev.reverse, p.next h)
  else if p.get h = '{' then .error (.unsupported "nested replacement fields in a format spec")
  else takeFieldAt (p.next h) (p.get h :: accRev)
termination_by (rest p).length
decreasing_by exact rest_next_length p h

theorem takeFieldAt_eq (p : s.Pos) (accRev : List Char) :
    (takeFieldAt p accRev).map (fun x => (x.1, rest x.2)) =
      (takeField (rest p)).map (fun x => (accRev.reverse ++ x.1, x.2)) := by
  induction p using rest_induction generalizing accRev with
  | step p ih =>
    rw [takeFieldAt]
    split
    · subst_vars; simp [rest_endPos, takeField, Except.map]
    · rename_i h
      rw [rest_next p h, takeField]
      split
      · simp [Except.map]
      · split
        · simp [Except.map]
        · rw [ih _ (rest_next_length p h)]
          cases takeField (rest (p.next h)) <;> simp [Except.map]

/-- The field whose `{` comes just before `q`: its rendering, the numbering
after it and the position after its `}`. -/
def fieldAt (pos : Array FormatArg) (named : Std.HashMap String FormatArg) (st : Numbering)
    (q : s.Pos) : Except FormatError (Markup × Numbering × s.Pos) :=
  -- The guard is `takeFieldAt`'s own first case; stated here, it keeps the
  -- elaborator from unfolding `takeFieldAt` when `fmtGo` matches on this.
  if q = s.endPos then .error (.badTemplate "expected '}' before end of string")
  else
    match takeFieldAt q [] with
    | .error e => .error e
    | .ok (field, r) =>
      match renderFieldA pos named st field with
      | .error e => .error e
      | .ok (m, st') => .ok (m, st', r)

theorem fieldAt_length {pos : Array FormatArg} {named : Std.HashMap String FormatArg} {st : Numbering}
    {q : s.Pos} {m : Markup} {st' : Numbering} {r : s.Pos}
    (h : fieldAt pos named st q = .ok (m, st', r)) : (rest r).length < (rest q).length := by
  unfold fieldAt at h
  have he := takeFieldAt_eq q []
  split at h
  · cases h
  split at h
  · cases h
  · rename_i field r' hf
    split at h
    · cases h
    · cases h
      rw [hf] at he
      cases ht : takeField (rest q) with
      | error e => rw [ht] at he; simp [Except.map] at he
      | ok x =>
        rw [ht] at he; simp [Except.map] at he
        have := takeField_length ht
        rw [he.2]; exact this

/-- `formatList`, in place: append the rendering of the template text at `p`
to `acc`. -/
def fmtGo (pos : Array FormatArg) (named : Std.HashMap String FormatArg) (st : Numbering)
    (p : s.Pos) (acc : String) : Except FormatError String :=
  if h : p = s.endPos then .ok acc
  else if p.get h = '{' then
    if peek (p.next h) = some '{' then fmtGo pos named st (adv (p.next h)) (acc.push '{')
    else
      match _hf : fieldAt pos named st (p.next h) with
      | .error e => .error e
      | .ok (m, st', r) => fmtGo pos named st' r (acc ++ m.str)
  else if p.get h = '}' then
    if peek (p.next h) = some '}' then fmtGo pos named st (adv (p.next h)) (acc.push '}')
    else .error (.badTemplate "Single '}' encountered in format string")
  else fmtGo pos named st (p.next h) (acc.push (p.get h))
termination_by (rest p).length
decreasing_by
  · have := rest_next_length p h
    rw [rest_adv, List.length_tail]; omega
  · have := fieldAt_length _hf
    have := rest_next_length p h
    omega
  · have := rest_next_length p h
    rw [rest_adv, List.length_tail]; omega
  · exact rest_next_length p h

theorem fieldAt_eq (pos : List FormatArg) (named : List (String × FormatArg)) (st : Numbering)
    (q : s.Pos) :
    (fieldAt pos.toArray (namedMap named) st q).map (fun x => (x.1, x.2.1, rest x.2.2)) =
      fieldL pos named st (rest q) := by
  have he := takeFieldAt_eq q []
  unfold fieldAt fieldL
  split
  · subst_vars; simp [rest_endPos, takeField, Except.map]
  · cases ht : takeFieldAt q [] with
    | error e =>
      rw [ht] at he
      cases ht' : takeField (rest q) with
      | error e' => rw [ht'] at he; simp [Except.map] at he; simp [he, Except.map]
      | ok x => rw [ht'] at he; simp [Except.map] at he
    | ok x =>
      rw [ht] at he
      cases ht' : takeField (rest q) with
      | error e' => rw [ht'] at he; simp [Except.map] at he
      | ok y =>
        rw [ht'] at he; simp [Except.map] at he
        obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
        simp at he; obtain ⟨rfl, rfl⟩ := he
        simp only
        rw [renderFieldA_toArray]
        cases renderField pos named st x1 <;> simp [Except.map]

theorem fmtGo_eq (pos : List FormatArg) (named : List (String × FormatArg)) (st : Numbering)
    (p : s.Pos) (acc : String) :
    (fmtGo pos.toArray (namedMap named) st p acc).map String.toList =
      (formatList pos named st (rest p)).map (acc.toList ++ ·) := by
  induction p using rest_induction generalizing st acc with
  | step p ih =>
    rw [fmtGo]
    split
    · subst_vars; simp [rest_endPos, formatList, Except.map]
    · rename_i h
      have hlt := rest_next_length p h
      have hadv : (rest (adv (p.next h))).length < (rest p).length := by
        rw [rest_adv, List.length_tail]; omega
      have tailCase : ∀ (c : Char) (st : Numbering),
          (fmtGo pos.toArray (namedMap named) st (adv (p.next h)) (acc.push c)).map String.toList =
            (mapOk (c :: ·) (formatList pos named st (rest (p.next h)).tail)).map
              (acc.toList ++ ·) := by
        intro c st
        rw [ih _ hadv, rest_adv]
        cases formatList pos named st (rest (p.next h)).tail <;>
          simp [Except.map, mapOk, String.toList_push]
      rw [rest_next p h, peek_eq]
      by_cases hc : p.get h = '{'
      · rw [hc, formatList_lbrace]
        simp only [ite_true]
        by_cases hb : (rest (p.next h)).head? = some '{'
        · simp only [hb, ite_true]; exact tailCase '{' st
        · simp only [hb, ite_false]
          have he := fieldAt_eq pos named st (p.next h)
          split
          · rename_i e hf
            rw [hf] at he; simp only [Except.map] at he; rw [← he]; rfl
          · rename_i m st' r hf
            rw [hf] at he; simp only [Except.map] at he; rw [← he]
            simp only
            have := fieldAt_length hf
            rw [ih _ (by omega)]
            cases formatList pos named st' (rest r) <;>
              simp [Except.map, mapOk, String.toList_append]
      · by_cases hc' : p.get h = '}'
        · rw [hc', formatList]
          simp only [ite_true, show ('}' : Char) ≠ '{' by decide, ite_false]
          by_cases hb : (rest (p.next h)).head? = some '}'
          · simp only [hb, ite_true]; exact tailCase '}' st
          · simp only [hb, ite_false]; rfl
        · rw [formatList]
          simp only [hc, hc', ite_false]
          rw [ih _ hlt]
          cases formatList pos named st (rest (p.next h)) <;>
            simp [Except.map, mapOk, String.toList_push]

end Cursor

/-- `formatWith`, reading the template in place. -/
def Markup.formatWithFast (t : Markup) (pos : List FormatArg)
    (named : List (String × FormatArg) := []) : Except FormatError Markup :=
  match Cursor.fmtGo pos.toArray (namedMap named) .unset t.str.toSlice.startPos "" with
  | .ok o => .ok ⟨o⟩
  | .error e => .error e

/-- The executable `formatWith` is `formatWith`. -/
@[csimp] theorem Markup.formatWith_eq_fast : @Markup.formatWith = @Markup.formatWithFast := by
  funext t pos named
  unfold Markup.formatWith Markup.formatWithFast
  have he := Cursor.fmtGo_eq pos named .unset t.str.toSlice.startPos ""
  rw [Cursor.rest_startPos] at he
  simp only [String.toList_empty, List.nil_append, String.copy_toSlice] at he
  cases h1 : formatList pos named .unset t.str.toList with
  | error e =>
    rw [h1] at he
    cases h2 : Cursor.fmtGo pos.toArray (namedMap named) .unset t.str.toSlice.startPos "" with
    | error e' => rw [h2] at he; simp [Except.map] at he; simp [he]
    | ok o => rw [h2] at he; simp [Except.map] at he
  | ok o =>
    rw [h1] at he
    cases h2 : Cursor.fmtGo pos.toArray (namedMap named) .unset t.str.toSlice.startPos "" with
    | error e' => rw [h2] at he; simp [Except.map] at he
    | ok o' =>
      rw [h2] at he; simp [Except.map] at he
      simp only [Except.ok.injEq, Markup.mk.injEq]
      rw [← he]; simp

/-- Upstream `Markup.format_map`. -/
def Markup.formatMap (t : Markup) (named : List (String × FormatArg)) :
    Except FormatError Markup :=
  t.formatWith [] named

/-! ## `%` -/

/-- A `%` key up to its `)`, and the rest after it. -/
def takeKey : List Char → Option (List Char × List Char)
  | [] => none
  | c :: l =>
    if c = ')' then some ([], l)
    else match takeKey l with
      | some (k, r) => some (c :: k, r)
      | none => none

theorem takeKey_spec {l k r : List Char} (h : takeKey l = some (k, r)) :
    l = k ++ ')' :: r := by
  induction l generalizing k with
  | nil => simp [takeKey] at h
  | cons c l ih =>
    unfold takeKey at h
    split at h
    · cases h; simp_all
    · split at h
      · rename_i k' r' heq
        cases h; rw [ih heq]; rfl
      · cases h

theorem takeKey_length {l k r : List Char} (h : takeKey l = some (k, r)) :
    r.length < l.length := by
  rw [takeKey_spec h]; simp; omega

/-- The conversion a `%` conversion character asks for, or why not. -/
def percentConv (c : Char) : Except FormatError Conversion :=
  if c = 's' then .ok .percentStr
  else if c = 'd' ∨ c = 'i' then .ok .percentInt
  else if ['r', 'a', 'c', 'x', 'X', 'o', 'e', 'E', 'f', 'F', 'g', 'G', 'u', '-', '+', ' ', '#',
      '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '.', '*'].contains c then
    .error (.unsupported s!"%-format conversion, flag or width '{c}'")
  else .error (.badTemplate s!"unsupported format character '{c}'")

/-- The `%` engine. `map` is the mapping for `%(key)s` fields, if the
arguments are a mapping; `rem` the positional arguments not yet used. -/
def percentList (map : Option (List (String × FormatArg))) :
    List FormatArg → List Char → Except FormatError (List Char)
  | rem, [] =>
    if map.isNone ∧ ¬ rem.isEmpty then .error .notAllConverted else .ok []
  | rem, c :: l =>
    if c = '%' then
      match hl : l with
      | [] => .error (.badTemplate "incomplete format")
      | d :: r =>
        if d = '%' then mapOk ('%' :: ·) (percentList map rem r)
        else if d = '(' then
          match h : takeKey r with
          | none => .error (.badTemplate "incomplete format key")
          | some (key, r') =>
            match r' with
            | [] => .error (.badTemplate "incomplete format")
            | cv :: r'' =>
              have : r''.length < r.length + 1 + 1 := by
                have := takeKey_length h; simp at this; omega
              match map with
              | none => .error .requiresMapping
              | some kv =>
                match percentConv cv with
                | .error e => .error e
                | .ok conv =>
                  match kv.lookup (String.ofList key) with
                  | none => .error (.missingKey (String.ofList key))
                  | some a =>
                    match a.render conv with
                    | .error e => .error e
                    | .ok m => mapOk (m.str.toList ++ ·) (percentList map rem r'')
        else
          match percentConv d with
          | .error e => .error e
          | .ok conv =>
            match map with
            | some _ => .error (.unsupported "a positional % field with mapping arguments")
            | none =>
              match rem with
              | [] => .error .notEnoughArguments
              | a :: rem' =>
                match a.render conv with
                | .error e => .error e
                | .ok m => mapOk (m.str.toList ++ ·) (percentList map rem' r)
    else mapOk (c :: ·) (percentList map rem l)
termination_by _ l => l.length

/-- `%` interpolation on markup, escaping every argument that is not already
safe (upstream `Markup.__mod__`). -/
def Markup.mod (t : Markup) (args : PercentArgs) : Except FormatError Markup :=
  let r := match args with
    | .tuple xs => percentList none xs t.str.toList
    | .mapping kv => percentList (some kv.reverse) [] t.str.toList
  match r with
  | .ok o => .ok ⟨String.ofList o⟩
  | .error e => .error e

/-! ### The executable `%` engine

As for `str.format`: `percGo` reads the template in place and appends to a
`String`; `mod_eq_fast` (`@[csimp]`) proves it equal to `Markup.mod`. -/

/-- One `%` field, given the text after its `%`: the rendering, the
positional arguments left and the text after the field. `map` looks a key
up in the mapping, if the arguments are one. -/
def percStepL (map : Option (String → Option FormatArg)) (rem : List FormatArg) :
    List Char → Except FormatError (Markup × List FormatArg × List Char)
  | [] => .error (.badTemplate "incomplete format")
  | d :: r =>
    if d = '%' then .ok (⟨"%"⟩, rem, r)
    else if d = '(' then
      match takeKey r with
      | none => .error (.badTemplate "incomplete format key")
      | some (key, r') =>
        match r' with
        | [] => .error (.badTemplate "incomplete format")
        | cv :: r'' =>
          match map with
          | none => .error .requiresMapping
          | some kv =>
            match percentConv cv with
            | .error e => .error e
            | .ok conv =>
              match kv (String.ofList key) with
              | none => .error (.missingKey (String.ofList key))
              | some a =>
                match a.render conv with
                | .error e => .error e
                | .ok m => .ok (m, rem, r'')
    else
      match percentConv d with
      | .error e => .error e
      | .ok conv =>
        match map with
        | some _ => .error (.unsupported "a positional % field with mapping arguments")
        | none =>
          match rem with
          | [] => .error .notEnoughArguments
          | a :: rem' =>
            match a.render conv with
            | .error e => .error e
            | .ok m => .ok (m, rem', r)

theorem percStepL_length {map : Option (String → Option FormatArg)} {rem rem' : List FormatArg}
    {l r : List Char} {m : Markup} (h : percStepL map rem l = .ok (m, rem', r)) :
    r.length < l.length := by
  unfold percStepL at h
  split at h
  · cases h
  · rename_i d r0
    split at h
    · cases h; simp
    · split at h
      · split at h
        · cases h
        · rename_i key r' hk
          have := takeKey_length hk
          split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · split at h
                · cases h
                · split at h
                  · cases h
                  · cases h; simp at this ⊢; omega
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · cases h; simp

theorem percentList_pct (map : Option (List (String × FormatArg))) (rem : List FormatArg)
    (l : List Char) :
    percentList map rem ('%' :: l) =
      match percStepL (map.map fun kv k => kv.lookup k) rem l with
      | .error e => .error e
      | .ok (m, rem', r) => mapOk (m.str.toList ++ ·) (percentList map rem' r) := by
  rw [percentList.eq_def]
  simp only [ite_true]
  match l with
  | [] => rfl
  | d :: r =>
    simp only [percStepL]
    by_cases h1 : d = '%'
    · subst h1; simp
    · simp only [h1, ite_false]
      by_cases h2 : d = '('
      · subst h2
        simp only [ite_true]
        split
        · rename_i hk; simp only [hk]
        · rename_i key r' hk
          simp only [hk]
          cases r' with
          | nil => rfl
          | cons cv r'' =>
            simp only
            cases map with
            | none => rfl
            | some kv =>
              simp only [Option.map_some]
              cases percentConv cv with
              | error e => rfl
              | ok conv =>
                simp only
                cases kv.lookup (String.ofList key) with
                | none => rfl
                | some a =>
                  simp only
                  cases a.render conv <;> rfl
      · simp only [h2, ite_false]
        cases percentConv d with
        | error e => rfl
        | ok conv =>
          simp only
          cases map with
          | some _ => simp
          | none =>
            simp only
            cases rem with
            | nil => rfl
            | cons a rem' =>
              simp only
              cases a.render conv <;> rfl

namespace Cursor

variable {s : String.Slice}

/-- `takeKey`, in place: the key (its characters in `accRev`, reversed, so
far) and the position after its `)`. -/
def takeKeyAt (p : s.Pos) (accRev : List Char) : Option (List Char × s.Pos) :=
  if h : p = s.endPos then none
  else if p.get h = ')' then some (accRev.reverse, p.next h)
  else takeKeyAt (p.next h) (p.get h :: accRev)
termination_by (rest p).length
decreasing_by exact rest_next_length p h

theorem takeKeyAt_eq (p : s.Pos) (accRev : List Char) :
    (takeKeyAt p accRev).map (fun x => (x.1, rest x.2)) =
      (takeKey (rest p)).map (fun x => (accRev.reverse ++ x.1, x.2)) := by
  induction p using rest_induction generalizing accRev with
  | step p ih =>
    rw [takeKeyAt]
    split
    · subst_vars; simp [rest_endPos, takeKey]
    · rename_i h
      rw [rest_next p h, takeKey]
      split
      · simp
      · rw [ih _ (rest_next_length p h)]
        cases takeKey (rest (p.next h)) <;> simp

/-- `percStepL`, in place. -/
def percStep (map : Option (Std.HashMap String FormatArg)) (rem : List FormatArg) (q : s.Pos) :
    Except FormatError (Markup × List FormatArg × s.Pos) :=
  if hq : q = s.endPos then .error (.badTemplate "incomplete format")
  else if q.get hq = '%' then .ok (⟨"%"⟩, rem, q.next hq)
  else if q.get hq = '(' then
    match takeKeyAt (q.next hq) [] with
    | none => .error (.badTemplate "incomplete format key")
    | some (key, r') =>
      if hr : r' = s.endPos then .error (.badTemplate "incomplete format")
      else
        match map with
        | none => .error .requiresMapping
        | some kv =>
          match percentConv (r'.get hr) with
          | .error e => .error e
          | .ok conv =>
            match kv[String.ofList key]? with
            | none => .error (.missingKey (String.ofList key))
            | some a =>
              match a.render conv with
              | .error e => .error e
              | .ok m => .ok (m, rem, r'.next hr)
  else
    match percentConv (q.get hq) with
    | .error e => .error e
    | .ok conv =>
      match map with
      | some _ => .error (.unsupported "a positional % field with mapping arguments")
      | none =>
        match rem with
        | [] => .error .notEnoughArguments
        | a :: rem' =>
          match a.render conv with
          | .error e => .error e
          | .ok m => .ok (m, rem', q.next hq)

theorem percStep_eq (map : Option (Std.HashMap String FormatArg)) (rem : List FormatArg)
    (q : s.Pos) :
    (percStep map rem q).map (fun x => (x.1, x.2.1, rest x.2.2)) =
      percStepL (map.map fun M k => M[k]?) rem (rest q) := by
  unfold percStep
  split
  · subst_vars; simp [rest_endPos, percStepL, Except.map]
  · rename_i hq
    rw [rest_next q hq, percStepL]
    by_cases h1 : q.get hq = '%'
    · simp [h1, Except.map]
    · simp only [h1, ite_false]
      by_cases h2 : q.get hq = '('
      · simp only [h2, ite_true]
        have hk := takeKeyAt_eq (q.next hq) []
        cases hka : takeKeyAt (q.next hq) [] with
        | none =>
          rw [hka] at hk
          cases hk' : takeKey (rest (q.next hq)) with
          | none => simp [Except.map]
          | some _ => rw [hk'] at hk; simp at hk
        | some kr =>
          obtain ⟨key, r'⟩ := kr
          rw [hka] at hk
          cases hk' : takeKey (rest (q.next hq)) with
          | none => rw [hk'] at hk; simp at hk
          | some kr' =>
            rw [hk'] at hk
            obtain ⟨key', r''⟩ := kr'
            simp at hk; obtain ⟨rfl, rfl⟩ := hk
            simp only
            split
            · subst_vars; simp [rest_endPos, Except.map]
            · rename_i hr
              rw [rest_next r' hr]
              simp only
              cases map with
              | none => simp [Except.map]
              | some kv =>
                simp only [Option.map_some]
                cases percentConv (r'.get hr) with
                | error e => simp [Except.map]
                | ok conv =>
                  simp only
                  cases kv[String.ofList key]? with
                  | none => simp [Except.map]
                  | some a =>
                    simp only
                    cases a.render conv <;> simp [Except.map]
      · simp only [h2, ite_false]
        cases percentConv (q.get hq) with
        | error e => simp [Except.map]
        | ok conv =>
          simp only
          cases map with
          | some _ => simp [Except.map]
          | none =>
            simp only
            cases rem with
            | nil => simp [Except.map]
            | cons a rem' =>
              simp only
              cases a.render conv <;> simp [Except.map]

theorem percStep_length {map : Option (Std.HashMap String FormatArg)} {rem rem' : List FormatArg}
    {q r : s.Pos} {m : Markup} (h : percStep map rem q = .ok (m, rem', r)) :
    (rest r).length < (rest q).length := by
  have he := percStep_eq map rem q
  rw [h] at he; simp only [Except.map] at he
  exact percStepL_length he.symm

/-- `percentList`, in place: append the rendering of the template text at
`p` to `acc`. -/
def percGo (map : Option (Std.HashMap String FormatArg)) (rem : List FormatArg) (p : s.Pos)
    (acc : String) : Except FormatError String :=
  if h : p = s.endPos then
    if map.isNone ∧ ¬ rem.isEmpty then .error .notAllConverted else .ok acc
  else if p.get h = '%' then
    match _hs : percStep map rem (p.next h) with
    | .error e => .error e
    | .ok (m, rem', r) => percGo map rem' r (acc ++ m.str)
  else percGo map rem (p.next h) (acc.push (p.get h))
termination_by (rest p).length
decreasing_by
  · have := percStep_length _hs
    have := rest_next_length p h
    omega
  · exact rest_next_length p h

/-- `percGo` over a hash map `M` that answers every key as `List.lookup` on
`map` does is `percentList` over `map`. -/
theorem percGo_eq (M : Option (Std.HashMap String FormatArg)) (map : Option (List (String × FormatArg)))
    (hM : M.map (fun M k => M[k]?) = map.map fun kv k => kv.lookup k) (rem : List FormatArg)
    (p : s.Pos) (acc : String) :
    (percGo M rem p acc).map String.toList =
      (percentList map rem (rest p)).map (acc.toList ++ ·) := by
  induction p using rest_induction generalizing rem acc with
  | step p ih =>
    rw [percGo]
    split
    · subst_vars; rw [rest_endPos, percentList]
      cases M <;> cases map <;> simp at hM <;> by_cases hr : rem = [] <;> simp_all [Except.map]
    · rename_i h
      have hlt := rest_next_length p h
      rw [rest_next p h]
      by_cases hc : p.get h = '%'
      · rw [hc, percentList_pct]
        simp only [ite_true]
        have he := percStep_eq M rem (p.next h)
        rw [hM] at he
        split
        · rename_i e hs
          rw [hs] at he; simp only [Except.map] at he; rw [← he]; rfl
        · rename_i m rem' r hs
          rw [hs] at he; simp only [Except.map] at he; rw [← he]
          simp only
          have := percStep_length hs
          rw [ih _ (by omega)]
          cases percentList map rem' (rest r) <;>
            simp [Except.map, mapOk, String.toList_append]
      · rw [percentList.eq_def]
        simp only [hc, ite_false]
        rw [ih _ hlt]
        cases percentList map rem (rest (p.next h)) <;>
          simp [Except.map, mapOk, String.toList_push]

end Cursor

/-- `Markup.mod`, reading the template in place. -/
def Markup.modFast (t : Markup) (args : PercentArgs) : Except FormatError Markup :=
  let r := match args with
    | .tuple xs => Cursor.percGo none xs t.str.toSlice.startPos ""
    | .mapping kv => Cursor.percGo (some (dictMap kv)) [] t.str.toSlice.startPos ""
  match r with
  | .ok o => .ok ⟨o⟩
  | .error e => .error e

theorem percGo_start (M : Option (Std.HashMap String FormatArg))
    (map : Option (List (String × FormatArg)))
    (hM : M.map (fun M k => M[k]?) = map.map fun kv k => kv.lookup k) (rem : List FormatArg)
    (t : String) :
    (Cursor.percGo M rem t.toSlice.startPos "").map String.toList =
      percentList map rem t.toList := by
  have he := Cursor.percGo_eq M map hM rem t.toSlice.startPos ""
  rw [Cursor.rest_startPos] at he
  simp only [String.toList_empty, List.nil_append, String.copy_toSlice] at he
  rw [he]; cases percentList map rem t.toList <;> rfl

/-- The executable `Markup.mod` is `Markup.mod`. -/
@[csimp] theorem Markup.mod_eq_fast : @Markup.mod = @Markup.modFast := by
  funext t args
  unfold Markup.mod Markup.modFast
  have key : ∀ (x : Except FormatError String) (y : Except FormatError (List Char)),
      x.map String.toList = y →
      (match y with | .ok o => Except.ok (Markup.mk (String.ofList o)) | .error e => .error e) =
        (match x with | .ok o => .ok (Markup.mk o) | .error e => .error e) := by
    intro x y h
    cases x <;> cases y <;> simp [Except.map] at h <;> simp [← h]
  cases args with
  | tuple xs => exact key _ _ (percGo_start none none rfl xs t.str)
  | mapping kv =>
    exact key _ _ (percGo_start (some (dictMap kv)) (some kv.reverse)
      (by simp only [Option.map_some, dictMap_get]) [] t.str)

/-- The arguments of `%` and `format`, written as upstream writes them: a
single value (a one-element tuple), a list or a tuple of values (positional
arguments), or a list of `(key, value)` pairs (a mapping, or keyword
arguments). -/
class ToPercentArgs (α : Type u) where
  toPercentArgs : α → PercentArgs

instance : ToPercentArgs PercentArgs := ⟨id⟩

instance (priority := low) {α : Type u} [ToFormatArg α] : ToPercentArgs α :=
  ⟨fun x => .tuple [ToFormatArg.toFormatArg x]⟩

instance {α : Type u} [ToFormatArg α] : ToPercentArgs (List α) :=
  ⟨fun xs => .tuple (xs.map ToFormatArg.toFormatArg)⟩

instance (priority := high) {α : Type u} [ToFormatArg α] : ToPercentArgs (List (String × α)) :=
  ⟨fun kv => .mapping (kv.map fun p => (p.1, ToFormatArg.toFormatArg p.2))⟩

/-- The values of a Lean tuple `(a, b, c)`, which nests as `a × (b × c)`. -/
class ToArgTuple (α : Type u) where
  toArgs : α → List FormatArg

instance (priority := low) {α : Type u} [ToFormatArg α] : ToArgTuple α :=
  ⟨fun x => [ToFormatArg.toFormatArg x]⟩

instance {α : Type u} {β : Type v} [ToFormatArg α] [ToArgTuple β] : ToArgTuple (α × β) :=
  ⟨fun p => ToFormatArg.toFormatArg p.1 :: ToArgTuple.toArgs p.2⟩

/-- `(a, b, ...)`: a tuple of values. -/
instance {α : Type u} {β : Type v} [ToFormatArg α] [ToArgTuple β] : ToPercentArgs (α × β) :=
  ⟨fun p => .tuple (ToArgTuple.toArgs p)⟩

/-- `t % args` (upstream `Markup.__mod__`): `Markup.mk "%s" % "<a>"`,
`t % ["<a>", "<b>"]`, `t % ("<a>", 3)`, `t % [("key", "<a>")]`. -/
instance {α : Type u} [ToPercentArgs α] : HMod Markup α (Except FormatError Markup) :=
  ⟨fun t x => t.mod (ToPercentArgs.toPercentArgs x)⟩

/-- Upstream `Markup.format(*args, **kwargs)`: `t.format "x"`,
`t.format (3, "x")`, `t.format [("name", "x")]`. With both positional and
keyword arguments, use `formatWith`. -/
def Markup.format {α : Type u} [ToPercentArgs α] (t : Markup) (args : α) :
    Except FormatError Markup :=
  let a := ToPercentArgs.toPercentArgs args
  t.formatWith a.pos a.named

/-- `format` is `formatWith` on the arguments' positional and keyword
lists, so every theorem about `formatWith` is a theorem about `format`. -/
theorem Markup.format_eq_formatWith {α : Type u} [ToPercentArgs α] (t : Markup) (args : α) :
    t.format args =
      t.formatWith (ToPercentArgs.toPercentArgs args).pos (ToPercentArgs.toPercentArgs args).named :=
  rfl

end LeanMarkupsafe
