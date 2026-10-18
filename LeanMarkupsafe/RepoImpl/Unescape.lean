import Std.Data.HashMap
import LeanMarkupsafe.DataTypes.Basic
import LeanMarkupsafe.RepoImpl.Entities

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

/-- Upstream `Markup.unescape`. -/
def Markup.unescape (m : Markup) : String := LeanMarkupsafe.unescape m.str

end LeanMarkupsafe
