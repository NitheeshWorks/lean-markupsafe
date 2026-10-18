import LeanMarkupsafe.Proofs.Closure

/-!
# Proofs: what `format` and `%` compute, for any template

`format_interpolates`, `mod_tuple_interpolates` and `mod_mapping_interpolates`
say that a successful interpolation of any template, trusted HTML included,
is the template's segments with literals copied, quotes unquoted, and the
`i`-th field replaced by the rendering of the argument it refers to
(`fieldRefs`): automatic fields take positions in order, `{3}` position 3,
`{name}`/`%(name)s` a keyword. `format_strings` specialises this to string
arguments, which appear as `escape s`. `format_closed` and `mod_closed` are
instances of `fill_escaped`.
-/

namespace LeanMarkupsafe

/-! ## Small facts about the engines' helpers -/

theorem takeField_noBrace {l f r : List Char} (h : takeField l = .ok (f, r)) :
    '{' ∉ f ∧ '}' ∉ f := by
  induction l generalizing f with
  | nil => simp [takeField] at h
  | cons c l ih =>
    unfold takeField at h
    split at h
    · cases h; simp
    · split at h
      · cases h
      · split at h
        · rename_i f' r' heq
          cases h
          obtain ⟨h1, h2⟩ := ih heq
          refine ⟨?_, ?_⟩ <;> intro hm <;> simp only [List.mem_cons] at hm <;>
            rcases hm with rfl | hm <;> simp_all
        · cases h

theorem takeKey_noParen {l k r : List Char} (h : takeKey l = some (k, r)) : ')' ∉ k := by
  induction l generalizing k with
  | nil => simp [takeKey] at h
  | cons c l ih =>
    unfold takeKey at h
    split at h
    · cases h; simp
    · split at h
      · rename_i k' r' heq
        cases h
        have := ih heq
        intro hm; simp only [List.mem_cons] at hm
        rcases hm with rfl | hm <;> simp_all
      · cases h

theorem Numbering.counter_step {st st' : Numbering} {fn : FieldName} (h : st.step fn = .ok st') :
    st'.counter = fn.next st.counter := by
  cases st <;> cases fn <;> simp [Numbering.step] at h <;> subst h <;> rfl

theorem resolveField_ok {pos : List FormatArg} {named : List (String × FormatArg)}
    {st : Numbering} {name : List Char} {a : FormatArg} {st' : Numbering}
    (h : resolveField pos named st name = .ok (a, st')) :
    ∃ fn, parseFieldName name = .ok fn ∧ (fn.ref st.counter).lookup pos named = some a ∧
      st'.counter = fn.next st.counter := by
  unfold resolveField at h
  split at h
  · cases h
  · rename_i fn hfn
    split at h
    · cases h
    · rename_i st'' hst
      split at h
      · rename_i a' ha
        cases h
        exact ⟨fn, hfn, ha, Numbering.counter_step hst⟩
      · split at h <;> cases h

/-- What one argument contributes to a field. -/
abbrev Renders (pos : List FormatArg) (named : List (String × FormatArg))
    (rc : ArgRef × Conversion) (m : Markup) : Prop :=
  ∃ a, rc.1.lookup pos named = some a ∧ a.render rc.2 = .ok m

/-! ## `str.format` -/

section Format
variable (pos : List FormatArg) (named : List (String × FormatArg))

theorem renderField_ok {st : Numbering} {field : List Char} {m : Markup} {st' : Numbering}
    (h : renderField pos named st field = .ok (m, st')) :
    ∃ fn, parseFieldName (splitField field).1 = .ok fn ∧
      Renders pos named (fn.ref st.counter, .brace (String.ofList (splitField field).2)) m ∧
      st'.counter = fn.next st.counter := by
  unfold renderField at h
  dsimp only at h
  split at h
  · cases h
  · rename_i a st'' hres
    split at h
    · cases h
    · rename_i m' hm
      cases h
      obtain ⟨fn, hfn, hlook, hc⟩ := resolveField_ok hres
      exact ⟨fn, hfn, ⟨a, hlook, hm⟩, hc⟩

/-- The engine-level interpolation statement for `str.format`. -/
theorem formatList_interpolates :
    ∀ (n : Nat) (l : List Char), l.length ≤ n → ∀ (st : Numbering) (out : List Char),
      formatList pos named st l = .ok out →
      ∃ segs ms, (∀ s ∈ segs, BraceSeg s) ∧ printSegs segs = l ∧
        Forall₂ (Renders pos named) (fieldRefsFrom st.counter segs) ms ∧ out = fillSegs segs ms := by
  intro n
  induction n with
  | zero =>
    intro l hl st out h
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rw [formatList] at h; cases h
    exact ⟨[], [], by simp, rfl, .nil, rfl⟩
  | succ n ih =>
    intro l hl st out h
    cases l with
    | nil =>
      rw [formatList] at h; cases h
      exact ⟨[], [], by simp, rfl, .nil, rfl⟩
    | cons c l =>
      simp only [List.length_cons] at hl
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
            obtain ⟨segs, ms, hwf, hp, hf, rfl⟩ := ih l (by simp at hl; omega) st o ho
            refine ⟨.quote ['{', '{'] '{' :: segs, ms, ?_, ?_, ?_, rfl⟩
            · intro s hs; simp at hs; rcases hs with rfl | hs
              · exact .inl ⟨rfl, rfl⟩
              · exact hwf s hs
            · simp [printSegs, Seg.src, hp]
            · exact hf
        · split at h
          · cases h
          · rename_i field r hfield
            split at h
            · cases h
            · rename_i m st' hrender
              obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
              have hlen' : r.length ≤ n := by have := takeField_length hfield; omega
              obtain ⟨segs, ms, hwf, hp, hf, rfl⟩ := ih r hlen' st' o ho
              obtain ⟨hnb1, hnb2⟩ := takeField_noBrace hfield
              obtain ⟨fn, hfn, hr, hc⟩ := renderField_ok pos named hrender
              refine ⟨.field ('{' :: field ++ ['}']) fn (.brace (String.ofList (splitField field).2))
                :: segs, m :: ms, ?_, ?_, ?_, ?_⟩
              · intro s hs; simp at hs; rcases hs with rfl | hs
                · exact ⟨field, rfl, hnb1, hnb2, hfn, rfl⟩
                · exact hwf s hs
              · simp [printSegs, Seg.src, hp, takeField_spec hfield]
              · simp only [fieldRefsFrom]; rw [← hc]; exact .cons hr hf
              · simp [fillSegs]
      · split at h
        · subst_vars
          split at h
          · rename_i hhd
            obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
            cases l with
            | nil => simp at hhd
            | cons d l =>
              simp at hhd; subst hhd
              obtain ⟨segs, ms, hwf, hp, hf, rfl⟩ := ih l (by simp at hl; omega) st o ho
              refine ⟨.quote ['}', '}'] '}' :: segs, ms, ?_, ?_, ?_, rfl⟩
              · intro s hs; simp at hs; rcases hs with rfl | hs
                · exact .inr ⟨rfl, rfl⟩
                · exact hwf s hs
              · simp [printSegs, Seg.src, hp]
              · exact hf
          · cases h
        · rename_i h1 h2
          obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
          obtain ⟨segs, ms, hwf, hp, hf, rfl⟩ := ih l (by omega) st o ho
          refine ⟨.text c :: segs, ms, ?_, ?_, hf, rfl⟩
          · intro s hs; simp at hs; rcases hs with rfl | hs
            · exact ⟨h1, h2⟩
            · exact hwf s hs
          · simp [printSegs, Seg.src, hp]

end Format

/-- `format_interpolates`. -/
theorem format_interpolates : Spec.formatInterpolates := by
  intro t pos named r h
  unfold Markup.format at h
  split at h
  · rename_i o ho
    cases h
    obtain ⟨segs, ms, hwf, hp, hf, rfl⟩ :=
      formatList_interpolates pos named _ _ (Nat.le_refl _) _ _ ho
    exact ⟨segs, ms, hwf, hp, hf, by simp⟩
  · cases h

/-! ## `%` -/

section Percent
variable (map : Option (List (String × FormatArg)))

theorem drop_eq_cons {xs rem : List FormatArg} {i : Nat} {a : FormatArg}
    (h : xs.drop i = a :: rem) : xs[i]? = some a ∧ rem = xs.drop (i + 1) := by
  constructor
  · rw [← List.head?_drop, h]; rfl
  · rw [← List.tail_drop, h]; rfl

/-- The engine-level interpolation statement for `%`. Positional fields
draw on `xs` from position `i`, the remaining positional arguments being
`rem`; keyed fields draw on the mapping `kv`. -/
theorem percentList_interpolates (xs : List FormatArg) (kv : List (String × FormatArg))
    (hmap : ∀ kv', map = some kv' → kv' = kv) :
    ∀ (n : Nat) (l : List Char), l.length ≤ n → ∀ (i : Nat) (rem : List FormatArg) (out : List Char),
      (map = none → rem = xs.drop i) → percentList map rem l = .ok out →
      ∃ segs ms, (∀ s ∈ segs, PercentSeg s) ∧ printSegs segs = l ∧
        Forall₂ (Renders xs kv) (fieldRefsFrom i segs) ms ∧ out = fillSegs segs ms ∧
        (map = none → autoCount segs = rem.length) := by
  intro n
  induction n with
  | zero =>
    intro l hl i rem out _ h
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; unfold percentList at h; split at h
    · cases h
    · rename_i hne; cases h
      refine ⟨[], [], by simp, rfl, .nil, rfl, fun hm => ?_⟩
      subst hm; simp at hne; simp [autoCount, hne]
  | succ n ih =>
    intro l hl i rem out hrem h
    cases l with
    | nil =>
      unfold percentList at h; split at h
      · cases h
      · rename_i hne; cases h
        refine ⟨[], [], by simp, rfl, .nil, rfl, fun hm => ?_⟩
        subst hm; simp at hne; simp [autoCount, hne]
    | cons c l =>
      simp only [List.length_cons] at hl
      rw [percentList.eq_def] at h; dsimp only at h
      split at h
      · subst_vars
        split at h
        · cases h
        · rename_i d r
          simp only [List.length_cons] at hl
          split at h
          · subst_vars
            obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
            obtain ⟨segs, ms, hwf, hp, hf, rfl, hc⟩ := ih r (by omega) i rem o hrem ho
            refine ⟨.quote ['%', '%'] '%' :: segs, ms, ?_, ?_, hf, rfl, ?_⟩
            · intro s hs; simp at hs; rcases hs with rfl | hs
              · exact ⟨rfl, rfl⟩
              · exact hwf s hs
            · simp [printSegs, Seg.src, hp]
            · simpa [autoCount] using hc
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
                · rename_i kv'
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
                        have hlen' : r''.length ≤ n := by
                          have := takeKey_length hkey; simp at this; omega
                        obtain ⟨segs, ms, hwf, hp, hf, rfl, hc⟩ :=
                          ih r'' hlen' i rem o hrem ho
                        have hkv := hmap kv' rfl; subst hkv
                        refine ⟨.field ('%' :: '(' :: key ++ [')', cv]) (.key (String.ofList key)) conv
                          :: segs, m :: ms, ?_, ?_, ?_, ?_, fun h => by cases h⟩
                        · intro s hs; simp at hs; rcases hs with rfl | hs
                          · exact ⟨cv, hconv, .inr ⟨key, takeKey_noParen hkey, rfl, rfl⟩⟩
                          · exact hwf s hs
                        · simp [printSegs, Seg.src, hp, takeKey_spec hkey]
                        · exact .cons ⟨a, hlook, hm⟩ hf
                        · simp [fillSegs]
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
                    obtain ⟨hxi, hrem'⟩ := drop_eq_cons (hrem rfl).symm
                    obtain ⟨segs, ms, hwf, hp, hf, rfl, hc⟩ :=
                      ih r (by omega) (i + 1) rem' o (fun _ => hrem') ho
                    refine ⟨.field ['%', d] .auto conv :: segs, m :: ms, ?_, ?_, ?_, ?_, ?_⟩
                    · intro s hs; simp at hs; rcases hs with rfl | hs
                      · exact ⟨d, hconv, .inl ⟨rfl, rfl⟩⟩
                      · exact hwf s hs
                    · simp [printSegs, Seg.src, hp]
                    · exact .cons ⟨a, hxi, hm⟩ hf
                    · simp [fillSegs]
                    · intro _; simp [autoCount, hc rfl]
      · rename_i h1
        obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
        obtain ⟨segs, ms, hwf, hp, hf, rfl, hc⟩ := ih l (by omega) i rem o hrem ho
        refine ⟨.text c :: segs, ms, ?_, ?_, hf, rfl, by simpa [autoCount] using hc⟩
        · intro s hs; simp at hs; rcases hs with rfl | hs
          · exact h1
          · exact hwf s hs
        · simp [printSegs, Seg.src, hp]

end Percent

/-- `mod_tuple_interpolates`. -/
theorem mod_tuple_interpolates : Spec.modTupleInterpolates := by
  intro t xs r h
  unfold Markup.mod at h
  dsimp only at h
  split at h
  · rename_i o ho
    cases h
    obtain ⟨segs, ms, hwf, hp, hf, rfl, hc⟩ :=
      percentList_interpolates none xs [] (by simp) _ _ (Nat.le_refl _) 0 xs o (by simp) ho
    exact ⟨segs, ms, hwf, hp, hf, by simp, hc rfl⟩
  · cases h

/-- `mod_mapping_interpolates`. -/
theorem mod_mapping_interpolates : Spec.modMappingInterpolates := by
  intro t kv r h
  unfold Markup.mod at h
  dsimp only at h
  split at h
  · rename_i o ho
    cases h
    obtain ⟨segs, ms, hwf, hp, hf, rfl, -⟩ :=
      percentList_interpolates (some kv) [] kv (by intro k h; cases h; rfl) _ _ (Nat.le_refl _)
        0 [] o (by simp) ho
    exact ⟨segs, ms, hwf, hp, hf, by simp⟩
  · cases h

/-! ## String arguments -/

theorem string_arg_rendering : Spec.stringArgRendering := by
  intro s c m h
  cases c with
  | percentStr => cases h; exact ⟨fun _ => rfl, fun h => by cases h⟩
  | percentInt =>
    refine ⟨fun h => absurd rfl h, fun _ => ?_⟩
    simp only [FormatArg.ofString, percentIntOfText] at h
    split at h
    · rename_i i hi; cases h; exact ⟨i, hi, rfl⟩
    · cases h
  | brace spec =>
    simp only [FormatArg.ofString] at h
    split at h
    · cases h; exact ⟨fun _ => rfl, fun h => by cases h⟩
    · cases h

theorem lookup_map_ofString (kv : List (String × String)) (k : String) :
    (kv.map fun p => (p.1, FormatArg.ofString p.2)).lookup k = (kv.lookup k).map .ofString := by
  induction kv with
  | nil => rfl
  | cons p kv ih =>
    simp only [List.map, List.lookup]
    split <;> simp_all

theorem lookup_strings {ss : List String} {kv : List (String × String)} {r : ArgRef}
    {a : FormatArg} (h : r.lookup (ss.map .ofString) (kv.map fun p => (p.1, .ofString p.2)) = some a) :
    ∃ s, r.lookupStr ss kv = some s ∧ a = .ofString s := by
  cases r with
  | pos i =>
    simp only [ArgRef.lookup, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨s, hs, rfl⟩
  | key k =>
    simp only [ArgRef.lookup, lookup_map_ofString, Option.map_eq_some_iff] at h
    obtain ⟨s, hs, rfl⟩ := h
    exact ⟨s, hs, rfl⟩

theorem fieldRefsFrom_brace : ∀ (n : Nat) (segs : List Seg), (∀ s ∈ segs, BraceSeg s) →
    ∀ rc ∈ fieldRefsFrom n segs, ∃ spec, rc.2 = .brace spec
  | _, [], _, _, h => by simp [fieldRefsFrom] at h
  | n, .text c :: r, hw, rc, h =>
    fieldRefsFrom_brace n r (fun s hs => hw s (by simp [hs])) rc (by simpa [fieldRefsFrom] using h)
  | n, .quote s c :: r, hw, rc, h =>
    fieldRefsFrom_brace n r (fun s hs => hw s (by simp [hs])) rc (by simpa [fieldRefsFrom] using h)
  | n, .field s fn conv :: r, hw, rc, h => by
    simp only [fieldRefsFrom, List.mem_cons] at h
    rcases h with rfl | h
    · obtain ⟨f, -, -, -, -, hc⟩ := hw (.field s fn conv) (by simp)
      exact ⟨_, hc⟩
    · exact fieldRefsFrom_brace _ r (fun s hs => hw s (by simp [hs])) rc h

theorem fieldRefsFrom_length : ∀ (n : Nat) (segs : List Seg),
    (fieldRefsFrom n segs).length = fieldCount segs
  | _, [] => rfl
  | n, .text _ :: r => by simp [fieldRefsFrom, fieldCount, fieldRefsFrom_length n r]
  | n, .quote _ _ :: r => by simp [fieldRefsFrom, fieldCount, fieldRefsFrom_length n r]
  | n, .field _ fn _ :: r => by simp [fieldRefsFrom, fieldCount, fieldRefsFrom_length (fn.next n) r]

/-- `format_strings`: with string arguments, each field becomes `escape` of
the string it refers to. -/
theorem format_strings : Spec.formatStrings := by
  intro t ss kv r h
  obtain ⟨segs, ms, hwf, hp, hf, hr⟩ := format_interpolates _ _ _ _ h
  have hf' := Forall₂.imp_mem (S := fun rc m => (∃ spec, rc.2 = .brace spec) ∧ Renders _ _ rc m)
    (fun rc hrc m hm => ⟨fieldRefsFrom_brace 0 segs hwf rc hrc, hm⟩) hf
  obtain ⟨args, hargs, rfl⟩ := Forall₂.factor (P := fun rc s => rc.1.lookupStr ss kv = some s)
    escape (fun rc m ⟨⟨spec, hspec⟩, a, ha, hm⟩ => by
      obtain ⟨s, hs, rfl⟩ := lookup_strings ha
      exact ⟨s, hs, (string_arg_rendering s _ m hm).1 (by rw [hspec]; simp)⟩) hf'
  refine ⟨segs, args, hwf, hp, ?_, hargs, ?_⟩
  · rw [← hargs.length_eq]; exact fieldRefsFrom_length 0 segs
  apply String.toList_inj.mp
  simp [hr]

/-! ## Closure under `format` and `%`, as instances of `fill_escaped` -/

theorem BraceSeg.delimited : ∀ {s : Seg}, BraceSeg s → s.Delimited
  | .text _, _ => trivial
  | .quote _ _, .inl ⟨rfl, rfl⟩ => ⟨rfl, '{', [], '{', rfl, by decide, by decide⟩
  | .quote _ _, .inr ⟨rfl, rfl⟩ => ⟨rfl, '}', [], '}', rfl, by decide, by decide⟩
  | .field _ _ _, ⟨f, rfl, _⟩ => ⟨'{', f, '}', rfl, by decide, by decide⟩

theorem percentConv_boundary' {cv : Char} {conv : Conversion} (h : percentConv cv = .ok conv) :
    IsBoundary cv := by
  unfold percentConv at h
  split at h
  · subst_vars; decide
  split at h
  · rename_i hd; rcases hd with rfl | rfl <;> decide
  split at h <;> cases h

theorem PercentSeg.delimited : ∀ {s : Seg}, PercentSeg s → s.Delimited
  | .text _, _ => trivial
  | .quote _ _, ⟨rfl, rfl⟩ => ⟨rfl, '%', [], '%', rfl, by decide, by decide⟩
  | .field _ _ _, ⟨cv, hcv, .inl ⟨rfl, _⟩⟩ =>
    ⟨'%', [], cv, rfl, by decide, percentConv_boundary' hcv⟩
  | .field _ _ _, ⟨cv, hcv, .inr ⟨k, _, rfl, _⟩⟩ =>
    ⟨'%', '(' :: k ++ [')'], cv, by simp, by decide, percentConv_boundary' hcv⟩

theorem ArgRef.lookup_mem {pos : List FormatArg} {named : List (String × FormatArg)} {r : ArgRef}
    {a : FormatArg} (h : r.lookup pos named = some a) : a ∈ pos ∨ ∃ k, (k, a) ∈ named := by
  cases r with
  | pos i => exact .inl (List.mem_of_getElem? h)
  | key k => exact .inr ⟨k, LeanMarkupsafe.lookup_mem h⟩

theorem fills_escaped {pos : List FormatArg} {named : List (String × FormatArg)}
    {segs : List Seg} {ms : List Markup} (hpos : ∀ a ∈ pos, a.Safe)
    (hnamed : ∀ p ∈ named, p.2.Safe) (hf : Fills pos named segs ms) :
    ∀ m ∈ ms, IsEscaped m.str := by
  intro m hm
  obtain ⟨rc, -, a, ha, hr⟩ := Forall₂.exists_of_mem hf m hm
  rcases ArgRef.lookup_mem ha with ha | ⟨k, hk⟩
  · exact hpos a ha _ _ hr
  · exact hnamed (k, a) hk _ _ hr

/-- `format` of an escaped-text template with safe arguments is escaped. -/
theorem format_closed : Spec.formatClosed := by
  intro t pos named r ht hpos hnamed h
  obtain ⟨segs, ms, hwf, hp, hf, hr⟩ := format_interpolates _ _ _ _ h
  show Esc r.str.toList
  rw [hr]
  exact fill_escaped ms (fills_escaped hpos hnamed hf) _ segs (Nat.le_refl _)
    (fun s hs => (hwf s hs).delimited) (hp ▸ ht)

/-- `%` of an escaped-text template with safe arguments is escaped. -/
theorem mod_closed : Spec.modClosed := by
  intro t xs kv r ht hxs hkv h
  rcases h with h | h
  · obtain ⟨segs, ms, hwf, hp, hf, hr, -⟩ := mod_tuple_interpolates _ _ _ h
    show Esc r.str.toList
    rw [hr]
    exact fill_escaped ms (fills_escaped hxs (by simp) hf) _ segs (Nat.le_refl _)
      (fun s hs => (hwf s hs).delimited) (hp ▸ ht)
  · obtain ⟨segs, ms, hwf, hp, hf, hr⟩ := mod_mapping_interpolates _ _ _ h
    show Esc r.str.toList
    rw [hr]
    exact fill_escaped ms (fills_escaped (by simp) hkv hf) _ segs (Nat.le_refl _)
      (fun s hs => (hwf s hs).delimited) (hp ▸ ht)

end LeanMarkupsafe
