import LeanMarkupsafe.Proofs.Escape
import LeanMarkupsafe.RepoImpl.Codec

/-!
# Proofs: escaping is a lawful Keel codec

`charCodec` pairs `escapeChar` with its decoder `escapedChar`; its law is one
case split. `escapeCodec := (Codec.many charCodec).map String.ofList
String.toList` is then lawful by construction, and its encoder is `escape`.
The round trips are instances of the codec law:

* `unescape_escape` from `Codec.decode_encode` and `unescape_decode`
  (on escaped text, `unescape` is the codec's decoder);
* `escape_injective` from `Codec.encode_injective`.
-/

namespace LeanMarkupsafe

open Keel

theorem escapedChar_escapeChar {ε : Type} [ParseError ε] (c : Char) (rest : List Char) :
    (escapedChar (ε := ε)).parse (escapeChar c ++ rest) = .ok c rest := by
  rw [escapeChar_eq]
  by_cases h1 : c = '&'
  · subst h1; simp [escapedChar]
    rw [show 'm' :: 'p' :: ';' :: rest = ['m', 'p', ';'] ++ rest from rfl, Parser.parse_lit]; rfl
  by_cases h2 : c = '<'
  · subst h2; simp [escapedChar]
    rw [show 't' :: ';' :: rest = ['t', ';'] ++ rest from rfl, Parser.parse_lit]; rfl
  by_cases h3 : c = '>'
  · subst h3; simp [escapedChar]
    rw [show 't' :: ';' :: rest = ['t', ';'] ++ rest from rfl, Parser.parse_lit]; rfl
  by_cases h4 : c = '"'
  · subst h4; simp [escapedChar]
    rw [show '3' :: '4' :: ';' :: rest = ['3'] ++ '4' :: ';' :: rest from rfl, Parser.parse_lit]
    simp
    rw [show ';' :: rest = [';'] ++ rest from rfl, Parser.parse_lit]; rfl
  by_cases h5 : c = '\''
  · subst h5; simp [escapedChar]
    rw [show '3' :: '9' :: ';' :: rest = ['3'] ++ '9' :: ';' :: rest from rfl, Parser.parse_lit]
    simp
    rw [show ';' :: rest = [';'] ++ rest from rfl, Parser.parse_lit]; rfl
  simp [escapedChar, h1, h2, h3, h4, h5, escapeChar_eq]

/-- One character: encoded by `escapeChar`, decoded by `escapedChar`. -/
def charCodec : Codec Char Char where
  encode := escapeChar
  parser := escapedChar
  valid _ := True
  follow _ := True
  parse_encode c rest _ _ := escapedChar_escapeChar c rest

theorem escapeChar_ne_nil (c : Char) : escapeChar c ≠ [] := by
  rw [escapeChar_eq]; split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> simp

theorem manyValid_charCodec : ∀ l : List Char, Codec.ManyValid charCodec l
  | [] => trivial
  | c :: l => ⟨trivial, escapeChar_ne_nil c, trivial, manyValid_charCodec l⟩

/-- **Escaping as a codec**: encoder `escape`, decoder reading escaped text
to the end. Lawful by construction (`Codec.many`, `Codec.map`). -/
def escapeCodec : Codec Char String :=
  (Codec.many charCodec).map String.ofList String.toList (fun _ => String.ofList_toList)

theorem flatMap_escapeChar (l : List Char) : l.flatMap escapeChar = escapeList l := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [ih]

/-- The codec's encoder is `escape`. -/
theorem escapeCodec_encode (s : String) : escapeCodec.encode s = (escape s).str.toList := by
  simp [escapeCodec, Codec.map, Codec.many, charCodec, flatMap_escapeChar]

theorem escapeCodec_valid (s : String) : escapeCodec.valid s := manyValid_charCodec s.toList

/-- The codec law for `escape`: decoding the escaped text gives the string
back and consumes everything. -/
theorem escapeCodec_decode_escape (s : String) :
    escapeCodec.decode (escape s).str.toList = some (s, []) := by
  have := escapeCodec.decode_encode (escapeCodec_valid s) (rest := []) rfl
  simpa [escapeCodec_encode] using this

/-- On escaped text, `unescape` is the codec's decoder. -/
theorem unescape_decode {t : String} (ht : IsEscaped t) :
    escapeCodec.decode t.toList = some (unescape t, []) := by
  have h := escapeCodec_decode_escape (unescape t)
  rwa [escape_unescape t ht] at h

/-- `unescape_escape`, as an instance of the codec law. -/
theorem unescape_escape : Spec.unescapeEscape := by
  intro s
  have h := unescape_decode (escape_sound s)
  rw [escapeCodec_decode_escape] at h
  simpa using h.symm

/-- `escape_injective`, as an instance of `Codec.encode_injective`. -/
theorem escape_injective : Spec.escapeInjective := fun s t h =>
  escapeCodec.encode_injective rfl (escapeCodec_valid s) (escapeCodec_valid t)
    (by rw [escapeCodec_encode, escapeCodec_encode, h])

end LeanMarkupsafe
