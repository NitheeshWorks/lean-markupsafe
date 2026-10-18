import LeanMarkupsafe.Proofs.Escape

/-!
# Proofs: `striptags`

* `striptags_no_tags`: after tag removal, no complete tag is left. The only
  `<` that can survive starts a tag or comment that is never closed, which is
  where upstream's scan stops too.
* `removeTags_no_lt`: text with no `<` is untouched.
* `striptags_eq`: `striptags` is the three passes in order.
-/

namespace LeanMarkupsafe

theorem removeTags_cons_of_ne {c : Char} (l : List Char) (h : c ≠ '<') :
    removeTags (c :: l) = c :: removeTags l := by
  rw [removeTags]; simp [h]

/-- `striptags_no_tags`: after tag removal no complete tag is left. -/
theorem striptags_no_tags : Spec.striptagsNoTags := by
  intro l
  induction h : l.length using Nat.strongRecOn generalizing l with
  | _ n ih =>
    cases l with
    | nil => rw [removeTags]; exact NoCompleteTag.nil
    | cons c l =>
      by_cases hc : c = '<'
      · subst hc
        rw [removeTags]
        simp only [ite_true]
        split
        · rename_i h3
          split
          · rename_i r hr
            have := findCommentEnd_length hr
            simp at this h
            exact ih r.length (by omega) r rfl
          · rename_i hr
            exact NoCompleteTag.unclosed (by unfold OpensUnclosed; simp [h3, hr])
        · rename_i h3
          split
          · rename_i r hr
            have := findClose_length hr
            simp at h
            exact ih r.length (by omega) r rfl
          · rename_i hr
            exact NoCompleteTag.unclosed (by unfold OpensUnclosed; simp [h3, hr])
      · rw [removeTags_cons_of_ne l hc]
        simp at h
        exact NoCompleteTag.cons hc (ih l.length (by omega) l rfl)

/-- Text without `<` passes tag removal unchanged. -/
theorem removeTags_no_lt : Spec.removeTagsNoLt := by
  intro l hl
  induction l with
  | nil => rw [removeTags]
  | cons c l ih =>
    have hc : c ≠ '<' := by intro h; subst h; simp at hl
    rw [removeTags_cons_of_ne l hc, ih (by simp_all)]

/-- `striptags` is tag removal, whitespace collapse, then `unescape`. -/
theorem striptags_eq : Spec.striptagsEq := fun _ => rfl

end LeanMarkupsafe
