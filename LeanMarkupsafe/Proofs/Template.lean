import LeanMarkupsafe.Proofs.Codec

/-!
# Proofs: the template theory

General facts about templates (`Seg`, `printSegs`, `fillSegs`) that both
interpolation engines instantiate:

* `Forall₂` helpers;
* `fill_escaped`: filling an escaped template whose delimiters are token
  boundaries with escaped renderings gives escaped text. `format_closed` and
  `mod_closed` are its two instances.
-/

namespace LeanMarkupsafe

/-! ## `Forall₂` -/

theorem Forall₂.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {as : List α} {bs : List β}, Forall₂ R as bs → Forall₂ S as bs
  | _, _, .nil => .nil
  | _, _, .cons hr hs => .cons (h _ _ hr) (Forall₂.imp h hs)

theorem Forall₂.imp_mem {α β : Type} {R S : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, (∀ a ∈ as, ∀ b, R a b → S a b) →
      Forall₂ R as bs → Forall₂ S as bs
  | _, _, _, .nil => .nil
  | _, _, h, .cons hr hs =>
    .cons (h _ (by simp) _ hr) (Forall₂.imp_mem (fun a ha => h a (by simp [ha])) hs)

theorem Forall₂.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Forall₂ R as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => by simp [hs.length_eq]

theorem Forall₂.exists_of_mem {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, Forall₂ R as bs → ∀ b ∈ bs, ∃ a ∈ as, R a b
  | _, _, .nil, _, hb => by simp at hb
  | _, _, .cons hr hs, b, hb => by
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, by simp, hr⟩
    · obtain ⟨a, ha, h⟩ := hs.exists_of_mem b hb
      exact ⟨a, by simp [ha], h⟩

/-- Pick a witness for each pair: a relation that factors through `f`. -/
theorem Forall₂.factor {α β γ : Type} {R : α → β → Prop} {P : α → γ → Prop} (f : γ → β)
    (h : ∀ a b, R a b → ∃ c, P a c ∧ b = f c) :
    ∀ {as : List α} {bs : List β}, Forall₂ R as bs → ∃ cs, Forall₂ P as cs ∧ bs = cs.map f
  | _, _, .nil => ⟨[], .nil, rfl⟩
  | _, _, .cons hr hs => by
    obtain ⟨c, hc, rfl⟩ := h _ _ hr
    obtain ⟨cs, hcs, rfl⟩ := Forall₂.factor f h hs
    exact ⟨c :: cs, .cons hc hcs, rfl⟩

/-! ## Delimited templates preserve escaping -/

/-- A character that is a token boundary in escaped text. -/
def IsBoundary (c : Char) : Prop := isEntityChar c = false ∧ c ≠ '&'

instance (c : Char) : Decidable (IsBoundary c) := inferInstanceAs (Decidable (_ ∧ _))

/-- A segment whose source starts and ends at token boundaries, and whose
quoted character is safe. -/
def Seg.Delimited : Seg → Prop
  | .text _ => True
  | .quote s c => isSpecial c = false ∧ ∃ a mid b, s = a :: (mid ++ [b]) ∧ IsBoundary a ∧ IsBoundary b
  | .field s _ _ => ∃ a mid b, s = a :: (mid ++ [b]) ∧ IsBoundary a ∧ IsBoundary b

theorem printSegs_append (a b : List Seg) : printSegs (a ++ b) = printSegs a ++ printSegs b := by
  induction a with
  | nil => rfl
  | cons s a ih => simp [printSegs, ih]

theorem printSegs_texts (w : List Char) : printSegs (w.map .text) = w := by
  induction w with
  | nil => rfl
  | cons c w ih => simp [printSegs, Seg.src, ih]

theorem fillSegs_texts (w : List Char) (r : List Seg) (ms : List Markup) :
    fillSegs (w.map .text ++ r) ms = w ++ fillSegs r ms := by
  induction w with
  | nil => rfl
  | cons c w ih => simp [fillSegs, ih]

/-- A prefix of the template text made of non-boundary characters is made
of text segments. -/
theorem texts_of_print_prefix :
    ∀ (w : List Char) {segs : List Seg} {R : List Char}, (∀ s ∈ segs, s.Delimited) →
      (∀ x ∈ w, ¬ IsBoundary x) → printSegs segs = w ++ R →
      ∃ rest, segs = w.map .text ++ rest ∧ printSegs rest = R ∧ ∀ s ∈ rest, s.Delimited
  | [], segs, _, hd, _, h => ⟨segs, rfl, by simpa using h, hd⟩
  | x :: w, [], _, _, _, h => by simp [printSegs] at h
  | x :: w, s :: segs, R, hd, hw, h => by
    cases s with
    | text c =>
      simp [printSegs, Seg.src] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rest, h1, h2, h3⟩ :=
        texts_of_print_prefix w (fun s hs => hd s (by simp [hs])) (fun y hy => hw y (by simp [hy])) h
      exact ⟨rest, by simp [h1], h2, h3⟩
    | quote src c =>
      obtain ⟨-, a, mid, b, rfl, ha, -⟩ := hd (.quote src c) (by simp)
      simp [printSegs, Seg.src] at h
      exact absurd (h.1 ▸ ha) (hw x (by simp))
    | field src fn conv =>
      obtain ⟨a, mid, b, rfl, ha, -⟩ := hd (.field src fn conv) (by simp)
      simp [printSegs, Seg.src] at h
      exact absurd (h.1 ▸ ha) (hw x (by simp))

theorem entity_tail_not_boundary : ∀ e ∈ entities, ∀ x ∈ e.tail, ¬ IsBoundary x := by
  intro e he
  simp only [entities, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> decide

theorem Esc.after_delimited {a b : Char} {mid post : List Char} (hb : IsBoundary b)
    (h : Esc (a :: (mid ++ [b]) ++ post)) : Esc post :=
  Esc.suffix_after hb.1 hb.2 h (a :: mid) post (by simp)

/-- The induction hypothesis of `fill_escaped`, for templates shorter than
`n` segments. -/
def FillsEscaped (n : Nat) : Prop :=
  ∀ (ms : List Markup), (∀ m ∈ ms, IsEscaped m.str) → ∀ segs : List Seg, segs.length ≤ n →
    (∀ s ∈ segs, s.Delimited) → Esc (printSegs segs) → Esc (fillSegs segs ms)

/-- A reference in the template is a run of text segments, copied whole. -/
theorem fill_escaped_amp {n : Nat} (ih : FillsEscaped n) {ms : List Markup}
    (hms : ∀ m ∈ ms, IsEscaped m.str) {rest : List Seg} (hl : rest.length ≤ n)
    (hd : ∀ s ∈ rest, s.Delimited) (he : Esc ('&' :: printSegs rest)) :
    Esc (fillSegs (.text '&' :: rest) ms) := by
  obtain ⟨e, hmem, R, heq, hR⟩ := Esc.amp_inv he
  obtain ⟨t, rfl⟩ := entities_head e hmem
  simp only [List.cons_append, List.cons.injEq, true_and] at heq
  obtain ⟨rest', rfl, h2, h3⟩ :=
    texts_of_print_prefix t hd (by simpa using entity_tail_not_boundary _ hmem) heq
  simp only [fillSegs, fillSegs_texts]
  exact Esc.ent hmem (ih ms hms rest' (by simp at hl; omega) h3 (h2 ▸ hR))

/-- One segment step of `fill_escaped`. -/
theorem fill_escaped_cons {n : Nat} (ih : FillsEscaped n) (ms : List Markup)
    (hms : ∀ m ∈ ms, IsEscaped m.str) (s : Seg) (rest : List Seg) (hl : rest.length ≤ n)
    (hd : ∀ x ∈ s :: rest, x.Delimited) (he : Esc (printSegs (s :: rest))) :
    Esc (fillSegs (s :: rest) ms) := by
  have hdr : ∀ x ∈ rest, x.Delimited := fun x hx => hd x (by simp [hx])
  simp only [printSegs] at he
  have hds := hd s (by simp)
  cases s with
  | text c =>
    by_cases hc : c = '&'
    · subst hc; exact fill_escaped_amp ih hms hl hdr he
    · obtain ⟨hs, hr⟩ := Esc.tail_of_ne_amp he hc
      exact Esc.char hs (ih ms hms rest hl hdr hr)
  | quote src c =>
    obtain ⟨hc, a, mid, b, rfl, -, hb⟩ := hds
    exact Esc.char hc (ih ms hms rest hl hdr (Esc.after_delimited hb he))
  | field src fn conv =>
    obtain ⟨a, mid, b, rfl, -, hb⟩ := hds
    have hr := Esc.after_delimited hb he
    cases ms with
    | nil => exact ih [] (by simp) rest hl hdr hr
    | cons m ms =>
      exact (hms m (by simp)).append (ih ms (fun x hx => hms x (by simp [hx])) rest hl hdr hr)

theorem fillsEscaped : ∀ n, FillsEscaped n
  | 0, _, _, [], _, _, _ => Esc.nil
  | 0, _, _, _ :: _, hl, _, _ => by simp at hl
  | _ + 1, _, _, [], _, _, _ => Esc.nil
  | n + 1, ms, hms, s :: rest, hl, hd, he =>
    fill_escaped_cons (fillsEscaped n) ms hms s rest (by simp at hl; omega) hd he

/-- `fill_escaped`: filling an escaped, delimited template with escaped
renderings gives escaped text. -/
theorem fill_escaped {segs : List Seg} {ms : List Markup} (hd : ∀ s ∈ segs, s.Delimited)
    (hms : ∀ m ∈ ms, IsEscaped m.str) (he : Esc (printSegs segs)) : Esc (fillSegs segs ms) :=
  fillsEscaped _ ms hms segs (Nat.le_refl _) hd he

end LeanMarkupsafe
