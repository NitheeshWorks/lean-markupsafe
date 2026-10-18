import LeanMarkupsafe.Proofs.Closure

/-!
# Proofs: provenance of `format` and `%` output, for any template

`format_provenance` and `mod_provenance` describe the output of a successful
interpolation of an arbitrary template, trusted HTML included. The template
splits into segments (`Seg`), and the output is those segments with literals
copied, quotes unquoted and each field replaced by an argument rendering.
With string arguments, `format_string_args_escaped` and
`mod_string_args_escaped` pin the inserted pieces down to `escape s`.
-/

namespace LeanMarkupsafe

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

theorem percentConv_cases {cv : Char} {conv : Conversion} (h : percentConv cv = .ok conv) :
    (cv = 's' ∨ cv = 'd' ∨ cv = 'i') ∧ IsPercentConv conv := by
  unfold percentConv at h
  split at h
  · cases h; exact ⟨.inl ‹_›, .inl rfl⟩
  split at h
  · cases h; rename_i hd; exact ⟨.inr hd, .inr rfl⟩
  split at h <;> cases h

/-! ## `str.format` -/

section Format
variable (pos : List FormatArg) (named : List (String × FormatArg))

theorem renderField_arg {st : Numbering} {field : List Char} {m : Markup} {st' : Numbering}
    (h : renderField pos named st field = .ok (m, st')) :
    ArgRendering IsBraceConv (pos ++ named.map Prod.snd) m := by
  unfold renderField at h
  dsimp only at h
  split at h
  · cases h
  · rename_i a st'' hres
    split at h
    · cases h
    · rename_i m' hm
      cases h
      refine ⟨a, ?_, _, ⟨_, rfl⟩, hm⟩
      rcases resolveField_mem pos named hres with ha | ⟨k, hk⟩
      · exact List.mem_append_left _ ha
      · exact List.mem_append_right _ (List.mem_map.mpr ⟨(k, a), hk, rfl⟩)

/-- The engine-level provenance statement for `str.format`. -/
theorem formatList_provenance :
    ∀ (n : Nat) (l : List Char), l.length ≤ n → ∀ (st : Numbering) (out : List Char),
      formatList pos named st l = .ok out →
      ∃ segs ms, (∀ s ∈ segs, BraceSeg s) ∧ printSegs segs = l ∧
        ms.length = fieldCount segs ∧ out = fillSegs segs ms ∧
        ∀ m ∈ ms, ArgRendering IsBraceConv (pos ++ named.map Prod.snd) m := by
  intro n
  induction n with
  | zero =>
    intro l hl st out h
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rw [formatList] at h; cases h
    exact ⟨[], [], by simp, rfl, rfl, rfl, by simp⟩
  | succ n ih =>
    intro l hl st out h
    cases l with
    | nil =>
      rw [formatList] at h; cases h
      exact ⟨[], [], by simp, rfl, rfl, rfl, by simp⟩
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
            obtain ⟨segs, ms, hwf, hp, hlen, hf, hm⟩ := ih l (by simp at hl; omega) st o ho
            refine ⟨.quote ['{', '{'] '{' :: segs, ms, ?_, ?_, ?_, ?_, hm⟩
            · intro s hs; simp at hs; rcases hs with rfl | hs
              · exact .inl ⟨rfl, rfl⟩
              · exact hwf s hs
            · simp [printSegs, Seg.src, hp]
            · simp [fieldCount, hlen]
            · simp [fillSegs, hf]
        · split at h
          · cases h
          · rename_i field r hfield
            split at h
            · cases h
            · rename_i m st' hrender
              obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
              have hlen' : r.length ≤ n := by have := takeField_length hfield; omega
              obtain ⟨segs, ms, hwf, hp, hlen, hf, hm⟩ := ih r hlen' st' o ho
              obtain ⟨hnb1, hnb2⟩ := takeField_noBrace hfield
              refine ⟨.field ('{' :: field ++ ['}']) :: segs, m :: ms, ?_, ?_, ?_, ?_, ?_⟩
              · intro s hs; simp at hs; rcases hs with rfl | hs
                · exact ⟨field, rfl, hnb1, hnb2⟩
                · exact hwf s hs
              · simp [printSegs, Seg.src, hp, takeField_spec hfield]
              · simp [fieldCount, hlen]
              · simp [fillSegs, hf]
              · intro m' hm'; simp at hm'; rcases hm' with rfl | hm'
                · exact renderField_arg pos named hrender
                · exact hm m' hm'
      · split at h
        · subst_vars
          split at h
          · rename_i hhd
            obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
            cases l with
            | nil => simp at hhd
            | cons d l =>
              simp at hhd; subst hhd
              obtain ⟨segs, ms, hwf, hp, hlen, hf, hm⟩ := ih l (by simp at hl; omega) st o ho
              refine ⟨.quote ['}', '}'] '}' :: segs, ms, ?_, ?_, ?_, ?_, hm⟩
              · intro s hs; simp at hs; rcases hs with rfl | hs
                · exact .inr ⟨rfl, rfl⟩
                · exact hwf s hs
              · simp [printSegs, Seg.src, hp]
              · simp [fieldCount, hlen]
              · simp [fillSegs, hf]
          · cases h
        · rename_i h1 h2
          obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
          obtain ⟨segs, ms, hwf, hp, hlen, hf, hm⟩ := ih l (by omega) st o ho
          refine ⟨.text c :: segs, ms, ?_, ?_, ?_, ?_, hm⟩
          · intro s hs; simp at hs; rcases hs with rfl | hs
            · exact ⟨h1, h2⟩
            · exact hwf s hs
          · simp [printSegs, Seg.src, hp]
          · simp [fieldCount, hlen]
          · simp [fillSegs, hf]

end Format

/-- `format_provenance`. -/
theorem format_provenance : Spec.formatProvenance := by
  intro t pos named r h
  unfold Markup.format at h
  split at h
  · rename_i o ho
    cases h
    obtain ⟨segs, ms, hwf, hp, hlen, hf, hm⟩ :=
      formatList_provenance pos named _ _ (Nat.le_refl _) _ _ ho
    exact ⟨segs, ms, hwf, hp, hlen, by simp [hf], hm⟩
  · cases h

/-! ## `%` -/

section Percent
variable (map : Option (List (String × FormatArg)))

/-- The engine-level provenance statement for `%`. `args` is the pool the
fields draw from: the remaining positional arguments and the mapping. -/
theorem percentList_provenance (args : List FormatArg)
    (hmap : ∀ kv, map = some kv → ∀ p ∈ kv, p.2 ∈ args) :
    ∀ (n : Nat) (l : List Char), l.length ≤ n → ∀ (rem : List FormatArg) (out : List Char),
      (∀ a ∈ rem, a ∈ args) → percentList map rem l = .ok out →
      ∃ segs ms, (∀ s ∈ segs, PercentSeg s) ∧ printSegs segs = l ∧
        ms.length = fieldCount segs ∧ out = fillSegs segs ms ∧
        ∀ m ∈ ms, ArgRendering IsPercentConv args m := by
  intro n
  induction n with
  | zero =>
    intro l hl rem out _ h
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; unfold percentList at h; split at h
    · cases h
    · cases h; exact ⟨[], [], by simp, rfl, rfl, rfl, by simp⟩
  | succ n ih =>
    intro l hl rem out hrem h
    cases l with
    | nil =>
      unfold percentList at h; split at h
      · cases h
      · cases h; exact ⟨[], [], by simp, rfl, rfl, rfl, by simp⟩
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
            obtain ⟨segs, ms, hwf, hp, hlen, hf, hm⟩ := ih r (by omega) rem o hrem ho
            refine ⟨.quote ['%', '%'] '%' :: segs, ms, ?_, ?_, ?_, ?_, hm⟩
            · intro s hs; simp at hs; rcases hs with rfl | hs
              · exact ⟨rfl, rfl⟩
              · exact hwf s hs
            · simp [printSegs, Seg.src, hp]
            · simp [fieldCount, hlen]
            · simp [fillSegs, hf]
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
                        have hlen' : r''.length ≤ n := by
                          have := takeKey_length hkey; simp at this; omega
                        obtain ⟨segs, ms, hwf, hp, hlen, hf, hms⟩ := ih r'' hlen' rem o hrem ho
                        obtain ⟨hcv, hconv'⟩ := percentConv_cases hconv
                        refine ⟨.field ('%' :: '(' :: key ++ [')', cv]) :: segs, m :: ms,
                          ?_, ?_, ?_, ?_, ?_⟩
                        · intro s hs; simp at hs; rcases hs with rfl | hs
                          · exact ⟨cv, hcv, .inr ⟨key, rfl, takeKey_noParen hkey⟩⟩
                          · exact hwf s hs
                        · simp [printSegs, Seg.src, hp, takeKey_spec hkey]
                        · simp [fieldCount, hlen]
                        · simp [fillSegs, hf]
                        · intro m' hm'; simp at hm'; rcases hm' with rfl | hm'
                          · exact ⟨a, hmap kv rfl _ (lookup_mem hlook), conv, hconv', hm⟩
                          · exact hms m' hm'
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
                    obtain ⟨segs, ms, hwf, hp, hlen, hf, hms⟩ :=
                      ih r (by omega) rem' o (fun x hx => hrem x (by simp [hx])) ho
                    obtain ⟨hcv, hconv'⟩ := percentConv_cases hconv
                    refine ⟨.field ['%', d] :: segs, m :: ms, ?_, ?_, ?_, ?_, ?_⟩
                    · intro s hs; simp at hs; rcases hs with rfl | hs
                      · exact ⟨d, hcv, .inl rfl⟩
                      · exact hwf s hs
                    · simp [printSegs, Seg.src, hp]
                    · simp [fieldCount, hlen]
                    · simp [fillSegs, hf]
                    · intro m' hm'; simp at hm'; rcases hm' with rfl | hm'
                      · exact ⟨a, hrem a (by simp), conv, hconv', hm⟩
                      · exact hms m' hm'
      · rename_i h1
        obtain ⟨o, ho, rfl⟩ := mapOk_eq_ok h
        obtain ⟨segs, ms, hwf, hp, hlen, hf, hm⟩ := ih l (by omega) rem o hrem ho
        refine ⟨.text c :: segs, ms, ?_, ?_, ?_, ?_, hm⟩
        · intro s hs; simp at hs; rcases hs with rfl | hs
          · exact h1
          · exact hwf s hs
        · simp [printSegs, Seg.src, hp]
        · simp [fieldCount, hlen]
        · simp [fillSegs, hf]

end Percent

/-- `mod_provenance`. -/
theorem mod_provenance : Spec.modProvenance := by
  intro t args r h
  unfold Markup.mod at h
  dsimp only at h
  split at h
  · rename_i o ho
    cases h
    have key : ∀ (map : Option (List (String × FormatArg))) (rem : List FormatArg),
        (∀ kv, map = some kv → ∀ p ∈ kv, p.2 ∈ args.toList) → (∀ a ∈ rem, a ∈ args.toList) →
        percentList map rem t.str.toList = .ok o →
        Provenance PercentSeg IsPercentConv args.toList t ⟨String.ofList o⟩ := by
      intro map rem hmap hrem hp
      obtain ⟨segs, ms, hwf, hpr, hlen, hf, hm⟩ :=
        percentList_provenance map args.toList hmap _ _ (Nat.le_refl _) rem o hrem hp
      exact ⟨segs, ms, hwf, hpr, hlen, by simp [hf], hm⟩
    cases args with
    | tuple xs => exact key none xs (by simp) (fun a ha => ha) ho
    | mapping kv =>
      exact key (some kv) [] (by
        intro kv' h p hp; cases h
        exact List.mem_map.mpr ⟨p, hp, rfl⟩) (by simp) ho
  · cases h

/-! ## String arguments are escaped -/

theorem string_arg_rendering : Spec.stringArgRendering := by
  intro s c m h
  cases c with
  | percentStr => cases h; exact ⟨fun _ => rfl, fun h => by cases h⟩
  | percentInt =>
    exact ⟨fun h => absurd rfl h, fun _ => percentIntOfText_ok h⟩
  | brace spec =>
    simp only [FormatArg.ofString] at h
    split at h
    · cases h; exact ⟨fun _ => rfl, fun h => by cases h⟩
    · cases h

/-- `format_string_args_escaped`. -/
theorem format_string_args_escaped : Spec.formatStringArgsEscaped := by
  intro t ss kv r h
  obtain ⟨segs, ms, hwf, hp, -, hf, hm⟩ := format_provenance _ _ _ _ h
  refine ⟨segs, ms, hwf, hp, hf, ?_⟩
  intro m hmem
  obtain ⟨a, ha, c, ⟨spec, rfl⟩, hr⟩ := hm m hmem
  simp only [List.mem_append, List.mem_map, List.map_map] at ha
  rcases ha with ⟨s, hs, rfl⟩ | ⟨p, hp', rfl⟩
  · exact ⟨s, by simp [hs], (string_arg_rendering s _ m hr).1 (by simp)⟩
  · exact ⟨p.2, by simp; exact .inr ⟨p.1, hp'⟩,
      (string_arg_rendering p.2 _ m hr).1 (by simp)⟩

/-- `mod_string_args_escaped`. -/
theorem mod_string_args_escaped : Spec.modStringArgsEscaped := by
  intro t ss r h
  obtain ⟨segs, ms, hwf, hp, -, hf, hm⟩ := mod_provenance _ _ _ h
  refine ⟨segs, ms, hwf, hp, hf, ?_⟩
  intro m hmem
  obtain ⟨a, ha, c, hc, hr⟩ := hm m hmem
  simp only [PercentArgs.toList, List.mem_map] at ha
  obtain ⟨s, hs, rfl⟩ := ha
  have := string_arg_rendering s c m hr
  rcases hc with rfl | rfl
  · exact .inl ⟨s, hs, this.1 (by simp)⟩
  · exact .inr (this.2 rfl)

end LeanMarkupsafe
