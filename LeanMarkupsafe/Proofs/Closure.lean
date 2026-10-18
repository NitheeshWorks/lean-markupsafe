import LeanMarkupsafe.Proofs.Escape

/-!
# Proofs: the invariant is closed under concatenation, `join`, `format`, `%`

The template engines copy literal text and insert argument renderings. An
escaped template's references contain none of `{`, `}`, `%`, so they are
copied whole; the characters that end a field (`}`, or the `%` conversion
character) are token boundaries (`Esc.suffix_after`), so the text after a
field is escaped again.
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

/-! ## `str.format` -/

section Format
variable (pos : List FormatArg) (named : List (String × FormatArg))

theorem formatList_lit (st : Numbering) {c : Char} (l : List Char) (h1 : c ≠ '{') (h2 : c ≠ '}') :
    formatList pos named st (c :: l) = mapOk (c :: ·) (formatList pos named st l) := by
  rw [formatList]; simp [h1, h2]

theorem formatList_entity (st : Numbering) {e : List Char} (he : e ∈ entities) (r : List Char) :
    formatList pos named st (e ++ r) = mapOk (e ++ ·) (formatList pos named st r) := by
  simp only [entities, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [List.cons_append, List.nil_append]
    repeat rw [formatList_lit pos named st _ (by decide) (by decide)]
    simp only [mapOk_mapOk]; rfl

theorem resolveField_mem {st : Numbering} {name : List Char} {a : FormatArg} {st' : Numbering}
    (h : resolveField pos named st name = .ok (a, st')) : a ∈ pos ∨ ∃ k, (k, a) ∈ named := by
  unfold resolveField at h
  repeat' (first | (split at h) | (dsimp only at h; split at h))
  all_goals first
    | (cases h; done)
    | (rename_i heq; cases h; exact .inl (List.mem_of_getElem? heq))
    | (rename_i heq; cases h; exact .inr ⟨_, lookup_mem heq⟩)

theorem renderField_safe (hpos : ∀ a ∈ pos, a.Safe) (hnamed : ∀ p ∈ named, p.2.Safe)
    {st : Numbering} {field : List Char} {m : Markup} {st' : Numbering}
    (h : renderField pos named st field = .ok (m, st')) : IsEscaped m.str := by
  unfold renderField at h
  dsimp only at h
  split at h
  · cases h
  · rename_i a st'' hres
    split at h
    · cases h
    · rename_i m' hm
      cases h
      rcases resolveField_mem pos named hres with ha | ⟨k, hk⟩
      · exact hpos a ha _ _ hm
      · exact hnamed (k, a) hk _ _ hm

theorem formatList_esc (hpos : ∀ a ∈ pos, a.Safe) (hnamed : ∀ p ∈ named, p.2.Safe) :
    ∀ (n : Nat) (l : List Char), l.length ≤ n → ∀ (st : Numbering) (out : List Char),
      Esc l → formatList pos named st l = .ok out → Esc out := by
  intro n
  induction n with
  | zero =>
    intro l hl st out _ h
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rw [formatList] at h; cases h; exact Esc.nil
  | succ n ih =>
    intro l hl st out hesc h
    cases l with
    | nil => rw [formatList] at h; cases h; exact Esc.nil
    | cons c l =>
      simp only [List.length_cons] at hl
      by_cases hamp : c = '&'
      · subst hamp
        obtain ⟨e, he, r, heq, hr⟩ := Esc.amp_inv hesc
        rw [heq, formatList_entity pos named st he] at h
        obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
        have hlen : r.length ≤ n := by
          have := congrArg List.length heq
          obtain ⟨t, rfl⟩ := entities_head e he
          simp at this; omega
        exact Esc.ent he (ih r hlen st o hr ho)
      · obtain ⟨hs, hl'⟩ := Esc.tail_of_ne_amp hesc hamp
        rw [formatList] at h
        split at h
        · subst_vars
          split at h
          · rename_i hhd
            obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
            cases l with
            | nil => simp at hhd
            | cons d l =>
              simp at hhd; subst hhd
              have := (Esc.tail_of_ne_amp hl' (by decide)).2
              exact Esc.char (by decide) (ih l (by simp at hl; omega) st o this ho)
          · split at h
            · cases h
            · rename_i field r hfield
              split at h
              · cases h
              · rename_i m st' hrender
                obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
                have hr : Esc r :=
                  Esc.suffix_after (c := '}') (by decide) (by decide) hl' field r
                    (takeField_spec hfield)
                have hlen : r.length ≤ n := by
                  have := takeField_length hfield; omega
                exact (renderField_safe pos named hpos hnamed hrender).append
                  (ih r hlen st' o hr ho)
        · split at h
          · subst_vars
            split at h
            · rename_i hhd
              obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
              cases l with
              | nil => simp at hhd
              | cons d l =>
                simp at hhd; subst hhd
                have := (Esc.tail_of_ne_amp hl' (by decide)).2
                exact Esc.char (by decide) (ih l (by simp at hl; omega) st o this ho)
            · cases h
          · obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
            exact Esc.char hs (ih l (by omega) st o hl' ho)

end Format

/-- `format` of an escaped template with safe arguments is escaped. -/
theorem format_closed : Spec.formatClosed := by
  intro t pos named r ht hpos hnamed h
  unfold Markup.format at h
  split at h
  · rename_i o ho
    cases h
    show Esc (String.ofList o).toList
    rw [String.toList_ofList]
    exact formatList_esc pos named hpos hnamed _ _ (Nat.le_refl _) _ _ ht ho
  · cases h

/-! ## `%` -/

section Percent
variable (map : Option (List (String × FormatArg)))

theorem percentList_lit (rem : List FormatArg) {c : Char} (l : List Char) (h1 : c ≠ '%') :
    percentList map rem (c :: l) = mapOk (c :: ·) (percentList map rem l) := by
  rw [percentList.eq_def]; simp [h1]

theorem percentList_entity (rem : List FormatArg) {e : List Char} (he : e ∈ entities)
    (r : List Char) :
    percentList map rem (e ++ r) = mapOk (e ++ ·) (percentList map rem r) := by
  simp only [entities, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
  · simp only [List.cons_append, List.nil_append]
    repeat rw [percentList_lit map rem _ (by decide)]
    simp only [mapOk_mapOk]; rfl

theorem percentConv_boundary {cv : Char} {conv : Conversion} (h : percentConv cv = .ok conv) :
    isEntityChar cv = false ∧ cv ≠ '&' := by
  unfold percentConv at h
  split at h
  · subst_vars; decide
  split at h
  · rename_i hd; rcases hd with rfl | rfl <;> decide
  split at h <;> cases h

theorem percentList_esc (hmap : ∀ kv, map = some kv → ∀ p ∈ kv, p.2.Safe) :
    ∀ (n : Nat) (l : List Char), l.length ≤ n → ∀ (rem : List FormatArg) (out : List Char),
      (∀ a ∈ rem, a.Safe) → Esc l → percentList map rem l = .ok out → Esc out := by
  intro n
  induction n with
  | zero =>
    intro l hl rem out _ _ h
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; unfold percentList at h; split at h
    · cases h
    · cases h; exact Esc.nil
  | succ n ih =>
    intro l hl rem out hrem hesc h
    cases l with
    | nil => unfold percentList at h; split at h
             · cases h
             · cases h; exact Esc.nil
    | cons c l =>
      simp only [List.length_cons] at hl
      by_cases hamp : c = '&'
      · subst hamp
        obtain ⟨e, he, r, heq, hr⟩ := Esc.amp_inv hesc
        rw [heq, percentList_entity map rem he] at h
        obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
        have hlen : r.length ≤ n := by
          have := congrArg List.length heq
          obtain ⟨t, rfl⟩ := entities_head e he
          simp at this; omega
        exact Esc.ent he (ih r hlen rem o hrem hr ho)
      · obtain ⟨hs, hl'⟩ := Esc.tail_of_ne_amp hesc hamp
        rw [percentList.eq_def] at h; dsimp only at h
        split at h
        · subst_vars
          split at h
          · cases h
          · rename_i d r
            by_cases hdamp : d = '&'
            · subst hdamp
              rw [show percentConv '&' = .error (.badTemplate "unsupported format character '&'")
                from rfl] at h
              simp at h
            obtain ⟨hsd, hr⟩ := Esc.tail_of_ne_amp hl' hdamp
            simp only [List.length_cons] at hl
            split at h
            · obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
              exact Esc.char (by decide) (ih r (by omega) rem o hrem hr ho)
            split at h
            · subst_vars
              split at h
              · cases h
              · rename_i key r' hkey
                split at h
                · cases h
                · rename_i cv r'' hkey
                  split at h
                  · cases h
                  · rename_i kv
                    split at h
                    · cases h
                    · rename_i conv hconv
                      split at h
                      · cases h
                      · rename_i a hlook
                        split at h
                        · cases h
                        · rename_i m hm
                          obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
                          have hb := percentConv_boundary hconv
                          have hr'' : Esc r'' :=
                            Esc.suffix_after hb.1 hb.2 hr (key ++ [')']) r''
                              (by rw [takeKey_spec hkey]; simp)
                          have hlen : r''.length ≤ n := by
                            have := takeKey_length hkey; simp at this; omega
                          have hsafe := hmap kv rfl (String.ofList key, a) (lookup_mem hlook)
                          exact (hsafe _ _ hm).append (ih r'' hlen rem o hrem hr'' ho)
            · split at h
              · cases h
              · rename_i conv hconv
                split at h
                · cases h
                · split at h
                  · cases h
                  · rename_i a rem'
                    split at h
                    · cases h
                    · rename_i m hm
                      obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
                      have hb := percentConv_boundary hconv
                      have hr2 : Esc r := Esc.suffix_after hb.1 hb.2 hl' [] r rfl
                      exact (hrem a (by simp) _ _ hm).append
                        (ih r (by omega) rem' o (fun x hx => hrem x (by simp [hx])) hr2 ho)
        · obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
          exact Esc.char hs (ih l (by omega) rem o hrem hl' ho)

end Percent

/-- `%` of an escaped template with safe arguments is escaped. -/
theorem mod_closed : Spec.modClosed := by
  intro t xs kv r ht hxs hkv h
  have key : ∀ (map : Option (List (String × FormatArg))) (rem : List FormatArg),
      (∀ kv', map = some kv' → ∀ p ∈ kv', p.2.Safe) → (∀ a ∈ rem, a.Safe) →
      (match percentList map rem t.str.toList with
        | .ok o => (Except.ok ⟨String.ofList o⟩ : Except FormatError Markup)
        | .error e => .error e) = .ok r → IsEscaped r.str := by
    intro map rem hmap hrem h
    split at h
    · rename_i o ho
      cases h
      show Esc (String.ofList o).toList
      rw [String.toList_ofList]
      exact percentList_esc map hmap _ _ (Nat.le_refl _) rem o hrem ht ho
    · cases h
  rcases h with h | h
  · exact key none xs (by simp) hxs h
  · exact key (some kv) [] (by intro kv' h; cases h; exact hkv) (by simp) h

end LeanMarkupsafe
