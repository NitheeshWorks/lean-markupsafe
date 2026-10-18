import LeanMarkupsafe.Proofs

/-!
# APIs

The public surface with its contracts in the types. Each function takes the
weakest precondition it needs and returns the strongest postcondition proved
for it, as a subtype or an `Except` of one. The plain functions
(`LeanMarkupsafe.escape`, `Markup.format`, ...) are the same computations
without the proofs attached; use these when a caller wants to carry the
invariant.
-/

namespace LeanMarkupsafe.API

open LeanMarkupsafe

/-- Escape a string: the result is escaped text, `unescape` gives the input
back, and its length is `escapedLength s`. -/
def escape (s : String) :
    {m : Markup // IsEscaped m.str ∧ LeanMarkupsafe.unescape m.str = s ∧
      m.str.length = escapedLength s} :=
  ⟨LeanMarkupsafe.escape s, escape_sound s, unescape_escape s, escape_length s⟩

/-- Escape a string, as an `Escaped` value. -/
def escapeE (s : String) : Escaped := ⟨LeanMarkupsafe.escape s, escape_sound s⟩

/-- Check whether a string is escaped text. -/
def checkEscaped (s : String) : Option {m : Escaped // m.val.str = s} :=
  if h : IsEscaped s then some ⟨⟨⟨s⟩, h⟩, rfl⟩ else none

/-- Unescape escaped text: the unique string that escapes to it. -/
def unescape (m : Escaped) : {s : String // LeanMarkupsafe.escape s = m.val} :=
  ⟨LeanMarkupsafe.unescape m.val.str, by
    obtain ⟨⟨s⟩, hs⟩ := m
    have h := escape_unescape s hs
    show LeanMarkupsafe.escape (LeanMarkupsafe.unescape s) = ⟨s⟩
    calc LeanMarkupsafe.escape (LeanMarkupsafe.unescape s)
        = ⟨(LeanMarkupsafe.escape (LeanMarkupsafe.unescape s)).str⟩ := rfl
      _ = ⟨s⟩ := by rw [h]⟩

/-- Concatenate escaped markup. -/
def append (a b : Escaped) : {m : Escaped // m.val = a.val ++ b.val} :=
  ⟨⟨a.val ++ b.val, concat_markup_markup _ _ a.property b.property⟩, rfl⟩

/-- Concatenate escaped markup and a plain string, escaping the string. -/
def appendString (a : Escaped) (s : String) :
    {m : Escaped // m.val.str = a.val.str ++ (LeanMarkupsafe.escape s).str} :=
  ⟨⟨a.val ++ s, (concat_string_closed a.val s a.property).1⟩, rfl⟩

/-- Join strings with an escaped separator, escaping each. -/
def join (sep : Escaped) (xs : List String) : {m : Escaped // m.val = Markup.join sep.val xs} :=
  ⟨⟨Markup.join sep.val xs, join_closed sep.val xs sep.property⟩, rfl⟩

/-- Join escaped markup with an escaped separator. -/
def joinEscaped (sep : Escaped) (xs : List Escaped) :
    {m : Escaped // m.val = Markup.join sep.val (xs.map Subtype.val)} :=
  ⟨⟨Markup.join sep.val (xs.map Subtype.val),
    join_markup_closed sep.val _ sep.property (by
      intro x hx; simp only [List.mem_map] at hx; obtain ⟨y, -, rfl⟩ := hx; exact y.property)⟩, rfl⟩

/-- A format argument whose every rendering is escaped text. -/
abbrev SafeArg := {a : FormatArg // a.Safe}

def SafeArg.ofString (s : String) : SafeArg := ⟨.ofString s, argsSafe_proof.1 s⟩
def SafeArg.ofInt (i : Int) : SafeArg := ⟨.ofInt i, argsSafe_proof.2.1 i⟩
def SafeArg.ofNat (n : Nat) : SafeArg := ⟨.ofNat n, argsSafe_proof.2.2.1 n⟩
def SafeArg.ofEscaped (m : Escaped) : SafeArg := ⟨.ofMarkup m.val, argsSafe_proof.2.2.2 m.val m.property⟩

private theorem safe_of_mem {xs : List SafeArg} : ∀ a ∈ xs.map Subtype.val, a.Safe := by
  intro a ha; simp only [List.mem_map] at ha; obtain ⟨b, -, rfl⟩ := ha; exact b.property

private theorem safe_of_mem_named {kv : List (String × SafeArg)} :
    ∀ p ∈ kv.map (fun p => (p.1, p.2.val)), p.2.Safe := by
  intro p hp; simp only [List.mem_map] at hp; obtain ⟨q, -, rfl⟩ := hp; exact q.2.property

/-- `str.format` on an escaped template with safe arguments: the result is
escaped, and it is what `Markup.format` returns. -/
def format (t : Escaped) (pos : List SafeArg) (named : List (String × SafeArg) := []) :
    Except FormatError
      {m : Escaped // t.val.format (pos.map Subtype.val) (named.map fun p => (p.1, p.2.val))
        = .ok m.val} :=
  match h : t.val.format (pos.map Subtype.val) (named.map fun p => (p.1, p.2.val)) with
  | .ok r => .ok ⟨⟨r, format_closed _ _ _ _ t.property safe_of_mem safe_of_mem_named h⟩, by first | exact h | rfl⟩
  | .error e => .error e

/-- `%` with a tuple of safe arguments on an escaped template. -/
def modTuple (t : Escaped) (xs : List SafeArg) :
    Except FormatError {m : Escaped // t.val.mod (.tuple (xs.map Subtype.val)) = .ok m.val} :=
  match h : t.val.mod (.tuple (xs.map Subtype.val)) with
  | .ok r => .ok ⟨⟨r, mod_closed _ _ [] _ t.property safe_of_mem (by simp) (.inl h)⟩, by first | exact h | rfl⟩
  | .error e => .error e

/-- `%` with a mapping of safe arguments on an escaped template. -/
def modMapping (t : Escaped) (kv : List (String × SafeArg)) :
    Except FormatError
      {m : Escaped // t.val.mod (.mapping (kv.map fun p => (p.1, p.2.val))) = .ok m.val} :=
  match h : t.val.mod (.mapping (kv.map fun p => (p.1, p.2.val))) with
  | .ok r => .ok ⟨⟨r, mod_closed _ [] _ _ t.property (by simp) safe_of_mem_named (.inr h)⟩, by first | exact h | rfl⟩
  | .error e => .error e

/-! ## Trusted templates

The functions above need an `Escaped` template. Real templates are trusted
HTML (`<em>{}</em>`); for those the guarantee is provenance: the output is
the template's own literal text with each field replaced by an argument's
rendering, and with string arguments each inserted piece is `escape s`. -/

/-- `str.format` on a trusted template: the result carries its provenance. -/
def formatTrusted (t : Markup) (pos : List FormatArg) (named : List (String × FormatArg) := []) :
    Except FormatError
      {r : Markup // Provenance BraceSeg IsBraceConv (pos ++ named.map Prod.snd) t r} :=
  match h : t.format pos named with
  | .ok r => .ok ⟨r, format_provenance t pos named r h⟩
  | .error e => .error e

/-- `str.format` on a trusted template with string arguments: the output is
the template's literal text with every field replaced by `escape s` for an
argument string `s`. -/
def formatStrings (t : Markup) (ss : List String) (kv : List (String × String) := []) :
    Except FormatError
      {r : Markup // ∃ segs ms, (∀ s ∈ segs, BraceSeg s) ∧ printSegs segs = t.str.toList ∧
        r.str.toList = fillSegs segs ms ∧ ∀ m ∈ ms, ∃ s ∈ ss ++ kv.map Prod.snd, m = escape s} :=
  match h : t.format (ss.map FormatArg.ofString) (kv.map fun p => (p.1, FormatArg.ofString p.2)) with
  | .ok r => .ok ⟨r, format_string_args_escaped t ss kv r h⟩
  | .error e => .error e

/-- `%` on a trusted template: the result carries its provenance. -/
def modTrusted (t : Markup) (args : PercentArgs) :
    Except FormatError {r : Markup // Provenance PercentSeg IsPercentConv args.toList t r} :=
  match h : t.mod args with
  | .ok r => .ok ⟨r, mod_provenance t args r h⟩
  | .error e => .error e

/-- `%` on a trusted template with string arguments: every inserted piece
is `escape s` (under `%s`) or an escaped integer (under `%d`). -/
def modStrings (t : Markup) (ss : List String) :
    Except FormatError
      {r : Markup // ∃ segs ms, (∀ s ∈ segs, PercentSeg s) ∧ printSegs segs = t.str.toList ∧
        r.str.toList = fillSegs segs ms ∧
        ∀ m ∈ ms, (∃ s ∈ ss, m = escape s) ∨ ∃ i : Int, m = escape (toString i)} :=
  match h : t.mod (.tuple (ss.map FormatArg.ofString)) with
  | .ok r => .ok ⟨r, mod_string_args_escaped t ss r h⟩
  | .error e => .error e

/-- `striptags`: the three passes, and no complete tag survives the first. -/
def striptags (m : Markup) :
    {s : String // s = LeanMarkupsafe.unescape (String.ofList (collapseSpaces (removeTags m.str.toList)))
      ∧ NoCompleteTag (removeTags m.str.toList)} :=
  ⟨m.striptags, striptags_eq m, striptags_no_tags _⟩

end LeanMarkupsafe.API
