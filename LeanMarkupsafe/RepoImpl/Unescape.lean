import Std.Data.HashMap
import LeanMarkupsafe.DataTypes.Basic
import LeanMarkupsafe.RepoImpl.Entities
import LeanMarkupsafe.RepoImpl.Cursor

/-!
# Unescaping: HTML character references

Upstream `Markup.unescape` is Python's `html.unescape`, which replaces every
match of

```
&(#[0-9]+;?|#[xX][0-9a-fA-F]+;?|[^\t\n\f <&#;]{1,32};?)
```

left to right, without rescanning a replacement:

* `#digits` / `#xhex`: the code point, except that the WHATWG "invalid
  character reference" table remaps 0x00, 0x0D and 0x80–0x9F, surrogates and
  values above 0x10FFFF become U+FFFD, and the noncharacters and most control
  characters vanish.
* a name: looked up in the HTML5 table (`Entities.raw`); failing that, the
  longest prefix of length at least 2 that is in the table is replaced and the
  rest kept; failing that, the text is kept.

Everything works on `List Char`; `decodeRef` reads the text after one `&`
and returns the replacement and the rest of the input.
-/

namespace LeanMarkupsafe

/-- Characters a named reference may contain: anything but tab, newline,
form feed, space, `<`, `&`, `#` and `;`. -/
def isNameChar (c : Char) : Bool :=
  !(c == '\t' || c == '\n' || c == '\x0c' || c == ' ' || c == '<' || c == '&' ||
    c == '#' || c == ';')

/-- ASCII decimal digit. -/
def isDecDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- ASCII hexadecimal digit. -/
def isHexDigit (c : Char) : Bool :=
  isDecDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- The longest prefix satisfying `p`, and the rest. -/
def spanChars (p : Char → Bool) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: l =>
    if p c then
      let r := spanChars p l
      (c :: r.1, r.2)
    else ([], c :: l)

/-- At most `n` name characters, and the rest (the regex's `{1,32}`). -/
def takeName : Nat → List Char → List Char × List Char
  | 0, l => ([], l)
  | _ + 1, [] => ([], [])
  | n + 1, c :: l =>
    if isNameChar c then
      let r := takeName n l
      (c :: r.1, r.2)
    else ([], c :: l)

/-- Drop one optional `;`. -/
def dropSemi : List Char → List Char
  | ';' :: l => l
  | l => l

/-- Value of a decimal digit string (most significant first). -/
def decValue (l : List Char) : Nat :=
  l.foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- Value of one hexadecimal digit. -/
def hexDigitValue (c : Char) : Nat :=
  if isDecDigit c then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- Value of a hexadecimal digit string. -/
def hexValue (l : List Char) : Nat :=
  l.foldl (fun n c => 16 * n + hexDigitValue c) 0

/-- The WHATWG remapping of invalid numeric references (Python's
`html._invalid_charrefs`). -/
def invalidCharref : List (Nat × Char) :=
  [(0x00, '�'), (0x0d, '\r'), (0x80, '€'), (0x81, '\x81'),
   (0x82, '‚'), (0x83, 'ƒ'), (0x84, '„'), (0x85, '…'),
   (0x86, '†'), (0x87, '‡'), (0x88, 'ˆ'), (0x89, '‰'),
   (0x8a, 'Š'), (0x8b, '‹'), (0x8c, 'Œ'), (0x8d, '\x8d'),
   (0x8e, 'Ž'), (0x8f, '\x8f'), (0x90, '\x90'), (0x91, '‘'),
   (0x92, '’'), (0x93, '“'), (0x94, '”'), (0x95, '•'),
   (0x96, '–'), (0x97, '—'), (0x98, '˜'), (0x99, '™'),
   (0x9a, 'š'), (0x9b, '›'), (0x9c, 'œ'), (0x9d, '\x9d'),
   (0x9e, 'ž'), (0x9f, 'Ÿ')]

/-- Code points a numeric reference deletes (Python's
`html._invalid_codepoints`): 0x01–0x08, 0x0B, 0x0E–0x1F, 0x7F–0x9F,
0xFDD0–0xFDEF, and the last two code points of every plane. -/
def isInvalidCodepoint (n : Nat) : Bool :=
  (1 ≤ n && n ≤ 8) || n == 0xb || (0xe ≤ n && n ≤ 0x1f) || (0x7f ≤ n && n ≤ 0x9f) ||
  (0xfdd0 ≤ n && n ≤ 0xfdef) || (n ≤ 0x10ffff && 0xfffe ≤ n % 0x10000)

/-- The replacement for a numeric reference with value `n`. -/
def numericRef (n : Nat) : List Char :=
  match invalidCharref.lookup n with
  | some c => [c]
  | none =>
    if (0xD800 ≤ n ∧ n ≤ 0xDFFF) ∨ 0x10FFFF < n then ['�']
    else if isInvalidCodepoint n then []
    else [Char.ofNat n]

/-- The HTML5 table, parsed once from `Entities.raw`. -/
def entityMap : Std.HashMap String String := Id.run do
  let mut m : Std.HashMap String String := {}
  for entry in Entities.raw.splitOn "\x00" do
    match entry.splitOn "\x01" with
    | [k, v] => m := m.insert k v
    | _ => pure ()
  return m

/-- Look a name (including its `;`, if any) up in the HTML5 table. The three
names `escape` produces take a fast path that the proofs reduce through; the
conformance suite checks it agrees with the table. -/
def lookupNamed (name : List Char) : Option (List Char) :=
  match name with
  | ['a', 'm', 'p', ';'] => some ['&']
  | ['l', 't', ';'] => some ['<']
  | ['g', 't', ';'] => some ['>']
  | _ => (entityMap.get? (String.ofList name)).map String.toList

/-- Python's fallback for an unknown name `s`: the longest prefix `s[:x]`,
`x` from `len(s) - 1` down to 2, that is in the table, followed by the rest of
`s`; failing that, `&` and `s` unchanged. -/
def prefixFallback (s : List Char) : Nat → List Char
  | 0 => '&' :: s
  | x + 1 =>
    if x + 1 < 2 then '&' :: s
    else match lookupNamed (s.take (x + 1)) with
      | some v => v ++ s.drop (x + 1)
      | none => prefixFallback s x

/-- The replacement for a named reference `s` (with its `;`, if any). -/
def namedRef (s : List Char) : List Char :=
  match lookupNamed s with
  | some v => v
  | none => prefixFallback s (s.length - 1)

/-- Decode the character reference at the start of `l`, the text after an
`&`: `some (replacement, rest)`, or `none` if no reference starts here (the
`&` is then literal). -/
def decodeRef (l : List Char) : Option (List Char × List Char) :=
  match l with
  | '#' :: r =>
    match r with
    | c :: r' =>
      if c = 'x' ∨ c = 'X' then
        let sp := spanChars isHexDigit r'
        if sp.1.isEmpty then none else some (numericRef (hexValue sp.1), dropSemi sp.2)
      else
        let sp := spanChars isDecDigit r
        if sp.1.isEmpty then none else some (numericRef (decValue sp.1), dropSemi sp.2)
    | [] => none
  | _ =>
    let tn := takeName 32 l
    if tn.1.isEmpty then none
    else match tn.2 with
      | ';' :: rest' => some (namedRef (tn.1 ++ [';']), rest')
      | _ => some (namedRef tn.1, tn.2)

theorem spanChars_snd_length (p : Char → Bool) (l : List Char) :
    (spanChars p l).2.length ≤ l.length := by
  induction l with
  | nil => simp [spanChars]
  | cons c l ih => unfold spanChars; split <;> simp <;> omega

theorem takeName_snd_length (n : Nat) (l : List Char) :
    (takeName n l).2.length ≤ l.length := by
  induction n generalizing l with
  | zero => simp [takeName]
  | succ n ih =>
    cases l with
    | nil => simp [takeName]
    | cons c l => unfold takeName; split <;> simp; have := ih l; omega

theorem dropSemi_length (l : List Char) : (dropSemi l).length ≤ l.length := by
  unfold dropSemi; split <;> simp

/-- A reference never lengthens the input: the rest is a suffix. -/
theorem decodeRef_length {l out r : List Char} (h : decodeRef l = some (out, r)) :
    r.length ≤ l.length := by
  unfold decodeRef at h
  split at h
  · rename_i r0
    split at h
    · rename_i c r'
      split at h
      · dsimp only at h
        split at h
        · simp at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          have := dropSemi_length (spanChars isHexDigit r').2
          have := spanChars_snd_length isHexDigit r'
          simp; omega
      · dsimp only at h
        split at h
        · simp at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          have := dropSemi_length (spanChars isDecDigit (c :: r')).2
          have := spanChars_snd_length isDecDigit (c :: r')
          simp at *; omega
    · simp at h
  · have := takeName_snd_length 32 l
    dsimp only at h
    split at h
    · simp at h
    · split at h
      · rename_i rest' heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        rw [heq] at this; simp at this; omega
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; exact this

/-- Upstream `html.unescape` on a character list. -/
def unescapeList : List Char → List Char
  | [] => []
  | c :: l =>
    if c = '&' then
      match h : decodeRef l with
      | some (out, r) =>
        have : r.length < l.length + 1 := Nat.lt_succ_of_le (decodeRef_length h)
        out ++ unescapeList r
      | none => '&' :: unescapeList l
    else c :: unescapeList l
termination_by l => l.length

/-- Replace HTML character references with the characters they represent
(upstream `Markup.unescape`, i.e. Python's `html.unescape`). -/
def unescape (s : String) : String := String.ofList (unescapeList s.toList)

/-! ### The executable unescape

`unescapeList` recurses once per character over a `List Char`. `unescapeFast`
reads the string in place through a `Cursor` and appends to a `String`, with
constant stack; numeric values saturate just above U+10FFFF, so a reference
with millions of digits costs linear time. `unescape_eq_fast` (`@[csimp]`)
proves it equal to `unescape`. -/

/-- Append characters to a string. -/
def pushList (acc : String) (l : List Char) : String := l.foldl String.push acc

theorem pushList_toList (acc : String) (l : List Char) :
    (pushList acc l).toList = acc.toList ++ l := by
  induction l generalizing acc with
  | nil => simp [pushList]
  | cons c l ih => simp [pushList] at *; rw [ih]; simp [String.toList_push]

/-- The largest code point; numeric values above it all decode to U+FFFD. -/
def maxCodepoint : Nat := 0x10FFFF

/-- One digit of a saturating fold: stops growing once above `maxCodepoint`. -/
def satStep (base : Nat) (dv : Char → Nat) (v : Nat) (c : Char) : Nat :=
  if maxCodepoint < v then v else base * v + dv c

theorem numericRef_big {n : Nat} (h : maxCodepoint < n) : numericRef n = ['�'] := by
  unfold numericRef
  have hl : invalidCharref.lookup n = none := by
    have hk : ∀ p ∈ invalidCharref, p.1 ≤ 0x9f := by decide
    generalize invalidCharref = xs at hk
    induction xs with
    | nil => rfl
    | cons p ps ih =>
      have := hk p (by simp)
      simp only [List.lookup]
      have hne : (n == p.1) = false := by
        simp [maxCodepoint] at h; simp; omega
      rw [hne]; exact ih (fun q hq => hk q (by simp [hq]))
  rw [hl]; simp only [maxCodepoint] at h
  simp [h]

theorem satFold_rel (base : Nat) (hb : 1 ≤ base) (dv : Char → Nat) (l : List Char) (a b : Nat)
    (h : (a ≤ maxCodepoint ∧ b = a) ∨ (maxCodepoint < a ∧ maxCodepoint < b)) :
    let a' := l.foldl (fun n c => base * n + dv c) a
    let b' := l.foldl (satStep base dv) b
    (a' ≤ maxCodepoint ∧ b' = a') ∨ (maxCodepoint < a' ∧ maxCodepoint < b') := by
  induction l generalizing a b with
  | nil => exact h
  | cons c l ih =>
    apply ih
    unfold satStep
    dsimp only
    rcases h with ⟨h1, hab⟩ | ⟨h1, h2⟩
    · subst hab
      rw [ite_eq_right (by omega)]
      by_cases hc : base * b + dv c ≤ maxCodepoint
      · exact Or.inl ⟨hc, rfl⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · rw [ite_eq_left h2]
      have : a ≤ base * a := Nat.le_mul_of_pos_left a hb
      exact Or.inr ⟨by omega, h2⟩

theorem numericRef_sat (base : Nat) (hb : 1 ≤ base) (dv : Char → Nat) (l : List Char) :
    numericRef (l.foldl (satStep base dv) 0) = numericRef (l.foldl (fun n c => base * n + dv c) 0) := by
  have := satFold_rel base hb dv l 0 0 (Or.inl ⟨by simp [maxCodepoint], rfl⟩)
  simp only at this
  rcases this with ⟨_, h⟩ | ⟨h1, h2⟩
  · rw [h]
  · rw [numericRef_big h1, numericRef_big h2]

theorem spanChars_eq (p : Char → Bool) (l : List Char) :
    spanChars p l = (l.takeWhile p, l.drop (l.takeWhile p).length) := by
  induction l with
  | nil => rfl
  | cons c l ih => unfold spanChars; by_cases h : p c <;> simp [h, ih]

theorem takeWhile_take (p : Char → Bool) (l : List Char) (n : Nat) :
    (l.take n).takeWhile p = (l.takeWhile p).take n := by
  induction l generalizing n with
  | nil => simp
  | cons c l ih =>
    cases n with
    | zero => simp
    | succ n => by_cases h : p c <;> simp [h, ih]

theorem takeName_eq (n : Nat) (l : List Char) :
    takeName n l = ((l.takeWhile isNameChar).take n,
      l.drop ((l.takeWhile isNameChar).take n).length) := by
  induction n generalizing l with
  | zero => simp [takeName]
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons c l =>
      unfold takeName
      by_cases h : isNameChar c <;> simp [h, ih]

theorem dropSemi_eq (l : List Char) : dropSemi l = if l.head? = some ';' then l.tail else l := by
  match l with
  | [] => rfl
  | c :: l => by_cases h : c = ';' <;> simp [dropSemi, h]

namespace Cursor

variable {s : String.Slice}

/-- Skip one `;`, if there is one (the cursor form of `dropSemi`). -/
def skipSemi (p : s.Pos) : s.Pos := if peek p = some ';' then adv p else p

theorem rest_skipSemi (p : s.Pos) : rest (skipSemi p) = dropSemi (rest p) := by
  unfold skipSemi; rw [dropSemi_eq, peek_eq]; split <;> simp_all [rest_adv]

/-- The run at `p` satisfying `P`, in one pass: `k` plus its length, its
saturating value in base `base` from `v`, and the position after it. -/
def scanNum (P : Char → Bool) (base : Nat) (dv : Char → Nat) (p : s.Pos) (k v : Nat) :
    Nat × Nat × s.Pos :=
  if h : p = s.endPos then (k, v, p)
  else if P (p.get h) then scanNum P base dv (p.next h) (k + 1) (satStep base dv v (p.get h))
  else (k, v, p)
termination_by (rest p).length
decreasing_by exact rest_next_length p h

theorem scanNum_eq (P : Char → Bool) (base : Nat) (dv : Char → Nat) (p : s.Pos) (k v : Nat) :
    (scanNum P base dv p k v).1 = k + ((rest p).takeWhile P).length ∧
    (scanNum P base dv p k v).2.1 = ((rest p).takeWhile P).foldl (satStep base dv) v ∧
    rest (scanNum P base dv p k v).2.2 = (rest p).drop ((rest p).takeWhile P).length := by
  induction p using rest_induction generalizing k v with
  | step p ih =>
    rw [scanNum]
    split
    · subst_vars; simp [rest_endPos]
    · rename_i h
      have hr := rest_next p h
      split
      · rename_i hc
        obtain ⟨a, b, c⟩ := ih _ (rest_next_length p h) (k + 1) (satStep base dv v (p.get h))
        rw [hr]; simp only [List.takeWhile_cons, hc, ite_true, List.length_cons, List.foldl_cons,
          List.drop_succ_cons]
        exact ⟨by rw [a]; omega, b, c⟩
      · rename_i hc
        have ht : (rest p).takeWhile P = [] := by rw [hr]; simp [hc]
        simp [ht]

/-- A numeric reference's digits at `p` in base `base`: the replacement and
where the reference ends, or `none` if there is no digit. -/
def numericAt (P : Char → Bool) (base : Nat) (dv : Char → Nat) (p : s.Pos) :
    Option (List Char × s.Pos) :=
  let r := scanNum P base dv p 0 0
  if r.1 = 0 then none
  else some (numericRef r.2.1, skipSemi r.2.2)

/-- At most `n` name characters at `p` (after `accRev`, reversed), and the
position after them: `takeName`, in one pass. -/
def scanName (p : s.Pos) : Nat → List Char → List Char × s.Pos
  | 0, acc => (acc.reverse, p)
  | n + 1, acc =>
    if h : p = s.endPos then (acc.reverse, p)
    else if isNameChar (p.get h) then scanName (p.next h) n (p.get h :: acc)
    else (acc.reverse, p)

theorem scanName_eq (p : s.Pos) (n : Nat) (acc : List Char) :
    (scanName p n acc).1 = acc.reverse ++ ((rest p).takeWhile isNameChar).take n ∧
      rest (scanName p n acc).2 = (rest p).drop (((rest p).takeWhile isNameChar).take n).length := by
  induction n generalizing p acc with
  | zero => simp [scanName]
  | succ n ih =>
    unfold scanName
    split
    · subst_vars; simp [rest_endPos]
    · rename_i h
      have := ih (p.next h) (p.get h :: acc)
      have hr := rest_next p h
      split
      · rename_i hc; rw [hr]; simp [hc, this]
      · rename_i hc
        have ht : (rest p).takeWhile isNameChar = [] := by rw [hr]; simp [hc]
        simp [ht]

/-- `decodeRef`, reading the text after an `&` in place. -/
def decodeAt (p : s.Pos) : Option (List Char × s.Pos) :=
  if peek p = some '#' then
    let p1 := adv p
    match peek p1 with
    | some c =>
      if c = 'x' ∨ c = 'X' then numericAt isHexDigit 16 hexDigitValue (adv p1)
      else numericAt isDecDigit 10 (fun c => c.toNat - '0'.toNat) p1
    | none => none
  else
    let sn := scanName p 32 []
    let name := sn.1
    if name.isEmpty then none
    else
      let q := sn.2
      if peek q = some ';' then some (namedRef (name ++ [';']), adv q)
      else some (namedRef name, q)

theorem take_takeWhile_length (P : Char → Bool) (l : List Char) :
    l.take (l.takeWhile P).length = l.takeWhile P := by
  induction l with
  | nil => rfl
  | cons c l ih => by_cases h : P c <;> simp [h, ih]

theorem numericAt_eq (P : Char → Bool) (base : Nat) (hb : 1 ≤ base) (dv : Char → Nat)
    (p : s.Pos) :
    (numericAt P base dv p).map (fun x => (x.1, rest x.2)) =
      (let sp := spanChars P (rest p)
       if sp.1.isEmpty then none
       else some (numericRef (sp.1.foldl (fun n c => base * n + dv c) 0), dropSemi sp.2)) := by
  unfold numericAt
  obtain ⟨h1, h2, h3⟩ := scanNum_eq P base dv p 0 0
  simp only [h1, Nat.zero_add, spanChars_eq]
  by_cases h : ((rest p).takeWhile P).length = 0
  · rw [ite_eq_left h, ite_eq_left (by simpa [List.isEmpty_iff, List.length_eq_zero_iff] using h)]; rfl
  · rw [ite_eq_right h, ite_eq_right (by simpa [List.isEmpty_iff, List.length_eq_zero_iff] using h)]
    simp only [Option.map_some, rest_skipSemi, h2, h3, numericRef_sat base hb]

theorem decodeRef_named {l : List Char} (h : l.head? ≠ some '#') :
    decodeRef l =
      (let tn := takeName 32 l
       if tn.1.isEmpty then none
       else match tn.2 with
         | ';' :: rest' => some (namedRef (tn.1 ++ [';']), rest')
         | _ => some (namedRef tn.1, tn.2)) := by
  unfold decodeRef
  split
  · simp at h
  · rfl

theorem decodeAt_eq (p : s.Pos) :
    (decodeAt p).map (fun x => (x.1, rest x.2)) = decodeRef (rest p) := by
  have h1 := rest_adv p
  have h2 := rest_adv (adv p)
  have hp1 := peek_eq (adv p)
  unfold decodeAt
  rw [peek_eq]
  generalize hr : rest p = l at h1
  by_cases hh : l.head? = some '#'
  · obtain ⟨r, rfl⟩ : ∃ r, l = '#' :: r := by
      cases l with
      | nil => simp at hh
      | cons c r => simp at hh; exact ⟨r, by rw [hh]⟩
    simp only [List.head?_cons, ite_true, List.tail_cons] at h1 ⊢
    rw [h1] at hp1 h2
    rw [hp1]
    match r with
    | c :: r' =>
      simp only [List.head?_cons, List.tail_cons] at h2 ⊢
      unfold decodeRef
      by_cases hx : c = 'x' ∨ c = 'X'
      · simp only [hx, ite_true]; rw [numericAt_eq _ _ (by decide), h2]; rfl
      · simp only [hx, ite_false]; rw [numericAt_eq _ _ (by decide), h1]; rfl
    | [] => simp [decodeRef]
  · rw [ite_eq_right hh, decodeRef_named hh, takeName_eq]
    obtain ⟨h1, h2⟩ := scanName_eq p 32 []
    rw [hr] at h1 h2
    simp only [List.reverse_nil, List.nil_append] at h1
    simp only [h1]
    generalize (scanName p 32 []).2 = q at h2 ⊢
    generalize (List.takeWhile isNameChar l).take 32 = name at h2 ⊢
    have hq := h2
    have hq' := peek_eq q
    have hq'' := rest_adv q
    rw [hq] at hq' hq''
    by_cases he : name.isEmpty
    · simp [he]
    · simp only [he, ite_false, Bool.false_eq_true]
      generalize l.drop name.length = t at hq hq' hq''
      match t with
      | ';' :: t' => simp [hq', hq'']
      | [] => simp [hq', hq]
      | c :: t' =>
        by_cases hc : c = ';'
        · subst hc; simp [hq', hq'']
        · simp [hq', hq, hc]

/-- `unescapeList`, in place: append the unescape of the text at `p` to `acc`. -/
def unescGo (p : s.Pos) (acc : String) : String :=
  if h : p = s.endPos then acc
  else
    if p.get h = '&' then
      match _hd : decodeAt (p.next h) with
      | some (out, r) => unescGo r (pushList acc out)
      | none => unescGo (p.next h) (acc.push '&')
    else unescGo (p.next h) (acc.push (p.get h))
termination_by (rest p).length
decreasing_by
  · have he := decodeAt_eq (p.next h)
    rw [_hd] at he
    simp only [Option.map_some] at he
    have := decodeRef_length he.symm
    have := rest_next_length p h
    omega
  · exact rest_next_length p h
  · exact rest_next_length p h

theorem unescGo_eq (p : s.Pos) (acc : String) :
    (unescGo p acc).toList = acc.toList ++ unescapeList (rest p) := by
  induction p using rest_induction generalizing acc with
  | step p ih =>
    unfold unescGo
    split
    · subst_vars; simp [rest_endPos, unescapeList]
    · rename_i h
      have hlt := rest_next_length p h
      rw [rest_next p h]
      split
      · rename_i hc
        rw [hc, unescapeList]
        simp only [ite_true]
        split
        · rename_i out r hd
          have he := decodeAt_eq (p.next h)
          rw [hd] at he
          simp only [Option.map_some] at he
          have hl := decodeRef_length he.symm
          rw [ih r (by omega), pushList_toList]
          split
          · rename_i out' r' hd'
            rw [← he] at hd'; simp at hd'; obtain ⟨rfl, rfl⟩ := hd'; simp
          · rename_i hd'; rw [← he] at hd'; simp at hd'
        · rename_i hd
          have he := decodeAt_eq (p.next h)
          rw [hd] at he
          rw [ih _ hlt]
          split
          · rename_i hd'; rw [← he] at hd'; simp at hd'
          · simp [String.toList_push]
      · rename_i hc
        rw [ih _ hlt, unescapeList]
        simp [hc, String.toList_push]

end Cursor

/-- `unescape`, reading the string in place (constant stack, linear time). -/
def unescapeFast (s : String) : String := Cursor.unescGo s.toSlice.startPos ""

/-- The executable unescape is `unescape`. -/
@[csimp] theorem unescape_eq_fast : @unescape = @unescapeFast := by
  funext s
  unfold unescape unescapeFast
  apply String.ext
  rw [Cursor.unescGo_eq, Cursor.rest_startPos]
  simp

/-- Upstream `Markup.unescape`. -/
def Markup.unescape (m : Markup) : String := LeanMarkupsafe.unescape m.str

end LeanMarkupsafe
