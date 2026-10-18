import LeanMarkupsafe.Specifications

/-!
# Proofs: escape, unescape and the `Esc` invariant

* `escape_sound`: `escape` output is `IsEscaped`.
* `escape_unescape`: `escape ∘ unescape = id` on escaped text, hence
  `isEscaped_iff` (escaped text is exactly the image of `escape`) and a
  `Decidable` instance for `IsEscaped`.
* `escape_length`: the exact length formula.
* `escape_markup_id` and the `soft_str` / `escape_silent` facts.
-/

namespace LeanMarkupsafe

/-! ## `escapeChar` as a chain of `if`s -/

theorem escapeChar_eq (c : Char) :
    escapeChar c =
      if c = '&' then ['&', 'a', 'm', 'p', ';']
      else if c = '<' then ['&', 'l', 't', ';']
      else if c = '>' then ['&', 'g', 't', ';']
      else if c = '"' then ['&', '#', '3', '4', ';']
      else if c = '\'' then ['&', '#', '3', '9', ';']
      else [c] := by
  unfold escapeChar
  split <;> simp_all

theorem escapeChar_of_not_special {c : Char} (h : isSpecial c = false) : escapeChar c = [c] := by
  simp only [isSpecial, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp [escapeChar_eq, h1, h2, h3, h4, h5]

@[simp] theorem escapeList_nil : escapeList [] = [] := rfl

@[simp] theorem escapeList_cons (c : Char) (l : List Char) :
    escapeList (c :: l) = escapeChar c ++ escapeList l := rfl

theorem escapeList_append (a b : List Char) :
    escapeList (a ++ b) = escapeList a ++ escapeList b := by
  induction a with
  | nil => rfl
  | cons c a ih => simp [ih]

@[simp] theorem escape_toList (s : String) : (escape s).str.toList = escapeList s.toList := by
  simp [escape]

/-! ## `Esc` algebra -/

theorem Esc.append {a b : List Char} (ha : Esc a) (hb : Esc b) : Esc (a ++ b) := by
  induction ha with
  | nil => exact hb
  | char hc _ ih => exact Esc.char hc ih
  | ent he _ ih => rw [List.append_assoc]; exact Esc.ent he ih

theorem Esc.escapeChar (c : Char) {l : List Char} (hl : Esc l) : Esc (LeanMarkupsafe.escapeChar c ++ l) := by
  rw [escapeChar_eq]
  split
  · exact Esc.ent (by simp [entities]) hl
  split
  · exact Esc.ent (by simp [entities]) hl
  split
  · exact Esc.ent (by simp [entities]) hl
  split
  · exact Esc.ent (by simp [entities]) hl
  split
  · exact Esc.ent (by simp [entities]) hl
  · refine Esc.char ?_ hl
    simp_all [isSpecial]

theorem Esc.escapeList (l : List Char) : Esc (LeanMarkupsafe.escapeList l) := by
  induction l with
  | nil => exact Esc.nil
  | cons c l ih => exact Esc.escapeChar c ih

/-- `escape_sound`: everything `escape` returns is escaped text. -/
theorem escape_sound : Spec.escapeSound := by
  intro s
  simp only [IsEscaped, escape_toList]
  exact Esc.escapeList _

/-- Every character of a reference is `&` or an `isEntityChar`. -/
theorem entities_chars : ∀ e ∈ entities, ∀ x ∈ e, x = '&' ∨ isEntityChar x = true := by
  intro e he
  simp only [entities, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Every reference starts with `&`. -/
theorem entities_head : ∀ e ∈ entities, ∃ t, e = '&' :: t := by
  intro e he
  simp only [entities, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- A non-`&` head of an escaped list is a safe character, and the tail is
escaped. -/
theorem Esc.tail_of_ne_amp {c : Char} {l : List Char} (h : Esc (c :: l)) (hc : c ≠ '&') :
    isSpecial c = false ∧ Esc l := by
  generalize hL : c :: l = L at h
  cases h with
  | nil => cases hL
  | char hs hl => cases hL; exact ⟨hs, hl⟩
  | ent he _ =>
    obtain ⟨t, rfl⟩ := entities_head _ he
    simp at hL; exact absurd hL.1 hc

/-- An `&` in an escaped list starts one of the five references. -/
theorem Esc.amp_inv {l : List Char} (h : Esc ('&' :: l)) :
    ∃ e ∈ entities, ∃ r, '&' :: l = e ++ r ∧ Esc r := by
  generalize hL : '&' :: l = L at h
  cases h with
  | nil => cases hL
  | char hs _ => cases hL; simp [isSpecial] at hs
  | ent he hl => exact ⟨_, he, _, rfl, hl⟩

/-- A boundary lemma: in an escaped list, the text after a character that
cannot occur inside a reference is escaped. -/
theorem Esc.suffix_after {c : Char} (hc : isEntityChar c = false) (hamp : c ≠ '&')
    {L : List Char} (hL : Esc L) : ∀ (pre post : List Char), L = pre ++ c :: post → Esc post := by
  induction hL with
  | nil => intro pre post h; simp at h
  | @char d l hd hl ih =>
    intro pre post h
    cases pre with
    | nil => simp at h; obtain ⟨rfl, rfl⟩ := h; exact hl
    | cons p pre => simp at h; obtain ⟨rfl, h⟩ := h; exact ih pre post h
  | @ent e l he hl ih =>
    intro pre post h
    rcases List.append_eq_append_iff.mp h with ⟨a', _, h2⟩ | ⟨c', h1, h2⟩
    · exact ih a' post h2
    · cases c' with
      | nil =>
        simp at h2; subst h2
        exact (Esc.tail_of_ne_amp hl hamp).2
      | cons d c' =>
        simp at h2; obtain ⟨rfl, -⟩ := h2
        exfalso
        have hmem : c ∈ e := by rw [h1]; simp
        rcases entities_chars e he c hmem with h | h
        · exact hamp h
        · rw [hc] at h; cases h

/-! ## `unescape` on the five references -/

theorem unescapeList_cons_of_ne {c : Char} (l : List Char) (h : c ≠ '&') :
    unescapeList (c :: l) = c :: unescapeList l := by
  rw [unescapeList]; simp [h]

theorem unescapeList_amp_of_decode {l out r : List Char} (h : decodeRef l = some (out, r)) :
    unescapeList ('&' :: l) = out ++ unescapeList r := by
  rw [unescapeList]
  simp only [ite_true]
  split
  · rename_i out' r' h'
    rw [h] at h'; cases h'; rfl
  · rename_i h'; rw [h] at h'; cases h'

theorem decodeRef_amp (r : List Char) : decodeRef ('a' :: 'm' :: 'p' :: ';' :: r) = some (['&'], r) := rfl
theorem decodeRef_lt (r : List Char) : decodeRef ('l' :: 't' :: ';' :: r) = some (['<'], r) := rfl
theorem decodeRef_gt (r : List Char) : decodeRef ('g' :: 't' :: ';' :: r) = some (['>'], r) := rfl
theorem decodeRef_quot (r : List Char) : decodeRef ('#' :: '3' :: '4' :: ';' :: r) = some (['"'], r) := rfl
theorem decodeRef_apos (r : List Char) : decodeRef ('#' :: '3' :: '9' :: ';' :: r) = some (['\''], r) := rfl

theorem escapeList_unescapeList {l : List Char} (h : Esc l) : escapeList (unescapeList l) = l := by
  induction h with
  | nil => rw [unescapeList]; rfl
  | @char c l hc _ ih =>
    have hne : c ≠ '&' := by intro h; subst h; simp [isSpecial] at hc
    rw [unescapeList_cons_of_ne l hne, escapeList_cons, ih, escapeChar_of_not_special hc]; rfl
  | @ent e l he _ ih =>
    simp only [entities, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · rw [show ['&', 'a', 'm', 'p', ';'] ++ l = '&' :: 'a' :: 'm' :: 'p' :: ';' :: l from rfl,
        unescapeList_amp_of_decode (decodeRef_amp l)]
      simp [ih]; rfl
    · rw [show ['&', 'l', 't', ';'] ++ l = '&' :: 'l' :: 't' :: ';' :: l from rfl,
        unescapeList_amp_of_decode (decodeRef_lt l)]
      simp [ih]; rfl
    · rw [show ['&', 'g', 't', ';'] ++ l = '&' :: 'g' :: 't' :: ';' :: l from rfl,
        unescapeList_amp_of_decode (decodeRef_gt l)]
      simp [ih]; rfl
    · rw [show ['&', '#', '3', '4', ';'] ++ l = '&' :: '#' :: '3' :: '4' :: ';' :: l from rfl,
        unescapeList_amp_of_decode (decodeRef_quot l)]
      simp [ih]; rfl
    · rw [show ['&', '#', '3', '9', ';'] ++ l = '&' :: '#' :: '3' :: '9' :: ';' :: l from rfl,
        unescapeList_amp_of_decode (decodeRef_apos l)]
      simp [ih]; rfl

/-- `escape_unescape`: on escaped text, escaping undoes unescaping. -/
theorem escape_unescape : Spec.escapeUnescape := by
  intro s hs
  apply String.toList_inj.mp
  simp [unescape, escapeList_unescapeList hs]

/-- Escaped text is exactly the image of `escape`. -/
theorem isEscaped_iff : Spec.isEscapedIffImage := by
  intro s
  constructor
  · intro h; exact ⟨unescape s, escape_unescape s h⟩
  · rintro ⟨t, rfl⟩; exact escape_sound t

theorem esc_iff_roundtrip (l : List Char) : Esc l ↔ escapeList (unescapeList l) = l := by
  constructor
  · exact escapeList_unescapeList
  · intro h; rw [← h]; exact Esc.escapeList _

instance (l : List Char) : Decidable (Esc l) := decidable_of_iff _ (esc_iff_roundtrip l).symm

instance (s : String) : Decidable (IsEscaped s) :=
  inferInstanceAs (Decidable (Esc s.toList))

/-! ## Length -/

theorem escapeList_length (l : List Char) :
    (escapeList l).length = l.length + 4 * l.count '&' + 3 * l.count '<' + 3 * l.count '>' +
      4 * l.count '"' + 4 * l.count '\'' := by
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [escapeList_cons, List.length_append, ih, List.count_cons, List.length_cons]
    rw [escapeChar_eq]
    by_cases h1 : c = '&'
    · subst h1; simp; omega
    by_cases h2 : c = '<'
    · subst h2; simp; omega
    by_cases h3 : c = '>'
    · subst h3; simp; omega
    by_cases h4 : c = '"'
    · subst h4; simp; omega
    by_cases h5 : c = '\''
    · subst h5; simp; omega
    simp [h1, h2, h3, h4, h5]
    omega

/-- `escape_length`: the exact length of the escaped text. -/
theorem escape_length : Spec.escapeLength := by
  intro s
  rw [← String.length_toList, escape_toList, escapeList_length, escapedLength,
    String.length_toList]

/-! ## Markup is not escaped again -/

/-- `escape_markup_id`: escaping markup returns it unchanged. -/
theorem escape_markup_id : Spec.escapeMarkupId := fun _ => rfl

theorem escape_string (s : String) : Markup.escape s = escape s := rfl

theorem softStr_markup : Spec.softStrMarkup := fun _ => ⟨rfl, rfl⟩

theorem escapeSilent_spec : Spec.escapeSilentSpec := ⟨rfl, fun _ => rfl⟩

-- `unescape_escape` and `escape_injective` are instances of the Keel codec
-- law, in `Proofs/Codec.lean`.

end LeanMarkupsafe
