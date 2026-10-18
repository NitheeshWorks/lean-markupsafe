import LeanMarkupsafe.Proofs.Template

/-!
# Proofs: the invariant is closed under concatenation and `join`

Both are instances of `Esc.append`. Closure under `format` and `%` is in
`Proofs/Provenance.lean`, as instances of `fill_escaped`.
-/

namespace LeanMarkupsafe

theorem isEscaped_append {a b : String} (ha : IsEscaped a) (hb : IsEscaped b) :
    IsEscaped (a ++ b) := by
  unfold IsEscaped at *; rw [String.toList_append]; exact ha.append hb

/-- `concat_markup_markup`: concatenation preserves the invariant. -/
theorem concat_markup_markup : Spec.appendClosed := by
  intro a b ha hb
  exact isEscaped_append ha hb

/-- Concatenating a plain string escapes it, on either side. -/
theorem concat_escapes : Spec.concatEscapes := fun _ _ => ⟨rfl, rfl⟩

/-- Concatenating escaped markup with a plain string stays escaped. -/
theorem concat_string_closed : Spec.concatStringClosed := by
  intro m s hm
  exact ⟨isEscaped_append hm (escape_sound s), isEscaped_append (escape_sound s) hm⟩

theorem Markup.concat_closed {α : Type u} [ToMarkup α] (m : Markup) (x : α)
    (hm : IsEscaped m.str) (hx : IsEscaped (Markup.escape x).str) :
    IsEscaped (m.concat x).str :=
  isEscaped_append hm hx

theorem joinMarkup_closed (sep : Markup) (hs : IsEscaped sep.str) :
    ∀ ms : List Markup, (∀ m ∈ ms, IsEscaped m.str) → IsEscaped (Markup.joinMarkup sep ms).str
  | [], _ => Esc.nil
  | [m], h => h m (by simp)
  | m :: m' :: ms, h => by
    simp only [Markup.joinMarkup, Markup.str_append]
    refine isEscaped_append (isEscaped_append (h m (by simp)) hs) ?_
    exact joinMarkup_closed sep hs (m' :: ms) (fun x hx => h x (by simp_all))

/-- `join` over markup items stays escaped when the separator and every item
are. -/
theorem join_markup_closed : Spec.joinMarkupClosed := by
  intro sep xs hs hx
  apply joinMarkup_closed sep hs
  intro m hm
  simp only [List.mem_map] at hm
  obtain ⟨x, hx', rfl⟩ := hm
  exact hx x hx'

/-- `join` with an escaped separator over strings is escaped. -/
theorem join_closed : Spec.joinClosed := by
  intro sep xs hs
  apply joinMarkup_closed sep hs
  intro m hm
  simp only [List.mem_map] at hm
  obtain ⟨x, -, rfl⟩ := hm
  exact escape_sound x

/-! ## Safe arguments -/

theorem percentIntOfText_ok {s : String} {m : Markup} (h : percentIntOfText s = .ok m) :
    ∃ i : Int, m = escape (toString i) := by
  unfold percentIntOfText at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h

theorem argsSafe_proof : Spec.argsSafe := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s c m h
    cases c with
    | percentStr => cases h; exact escape_sound s
    | percentInt =>
      obtain ⟨i, rfl⟩ := percentIntOfText_ok h; exact escape_sound _
    | brace spec =>
      simp only [FormatArg.ofString] at h
      split at h
      · cases h; exact escape_sound s
      · cases h
  · intro i c m h
    cases c with
    | percentStr => cases h; exact escape_sound _
    | percentInt => cases h; exact escape_sound _
    | brace spec =>
      simp only [FormatArg.ofInt] at h
      split at h
      · cases h; exact escape_sound _
      · cases h
  · intro n c m h
    cases c with
    | percentStr => cases h; exact escape_sound _
    | percentInt => cases h; exact escape_sound _
    | brace spec =>
      simp only [FormatArg.ofNat, FormatArg.ofInt] at h
      split at h
      · cases h; exact escape_sound _
      · cases h
  · intro mk hmk c m h
    cases c with
    | percentStr => cases h; exact hmk
    | percentInt =>
      obtain ⟨i, rfl⟩ := percentIntOfText_ok h; exact escape_sound _
    | brace spec =>
      simp only [FormatArg.ofMarkup] at h
      split at h
      · cases h; exact hmk
      · cases h

/-! ## `mapOk` -/

theorem mapOk_eq_ok {f : List Char → List Char} {x : Except FormatError (List Char)}
    {out : List Char} (h : mapOk f x = .ok out) : ∃ o, x = .ok o ∧ out = f o := by
  cases x with
  | ok o => exact ⟨o, rfl, by simp [mapOk] at h; exact h.symm⟩
  | error e => simp [mapOk] at h

theorem mapOk_mapOk (f g : List Char → List Char) (x : Except FormatError (List Char)) :
    mapOk f (mapOk g x) = mapOk (f ∘ g) x := by
  cases x <;> rfl

theorem lookup_mem {k : String} {a : FormatArg} :
    ∀ {kv : List (String × FormatArg)}, kv.lookup k = some a → (k, a) ∈ kv
  | [], h => by simp [List.lookup] at h
  | (k', a') :: kv, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i heq; cases h; simp at heq; simp [heq]
    · exact List.mem_cons_of_mem _ (lookup_mem h)

end LeanMarkupsafe
