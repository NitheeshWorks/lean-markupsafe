import LeanMarkupsafe.RepoImpl.Unescape

/-!
# `striptags` and whitespace splitting

Upstream `Markup.striptags` runs three passes:

1. remove tags: from each `<`, drop through the next `>`; from each `<!--`,
   drop through the next `-->` after it. An unclosed tag or comment stops the
   scan and the rest is kept verbatim.
2. collapse whitespace: `" ".join(value.split())`, where `split()` splits on
   runs of Unicode whitespace (`str.isspace`) and drops empty fields.
3. `unescape` the result.

`removeTags` is pass 1, `collapseSpaces` pass 2.
-/

namespace LeanMarkupsafe

/-- The rest of the input after the first `>`, if there is one. -/
def findClose : List Char → Option (List Char)
  | [] => none
  | c :: l => if c = '>' then some l else findClose l

/-- The rest of the input after the first `-->`, if there is one. -/
def findCommentEnd : List Char → Option (List Char)
  | [] => none
  | c :: l =>
    if c = '-' ∧ l.take 2 = ['-', '>'] then some (l.drop 2) else findCommentEnd l

theorem findClose_length {l r : List Char} (h : findClose l = some r) :
    r.length < l.length := by
  induction l with
  | nil => simp [findClose] at h
  | cons c l ih =>
    unfold findClose at h
    split at h
    · cases h; simp
    · have := ih h; simp; omega

theorem findCommentEnd_length {l r : List Char} (h : findCommentEnd l = some r) :
    r.length < l.length := by
  induction l with
  | nil => simp [findCommentEnd] at h
  | cons c l ih =>
    unfold findCommentEnd at h
    split at h
    · cases h; simp; omega
    · have := ih h; simp; omega

/-- Pass 1 of `striptags`: remove tags and comments. -/
def removeTags : List Char → List Char
  | [] => []
  | c :: l =>
    if c = '<' then
      if l.take 3 = ['!', '-', '-'] then
        match h : findCommentEnd (l.drop 3) with
        | some r =>
          have : r.length < l.length + 1 := by
            have := findCommentEnd_length h; simp at this; omega
          removeTags r
        | none => c :: l
      else
        match h : findClose l with
        | some r =>
          have : r.length < l.length + 1 := by have := findClose_length h; omega
          removeTags r
        | none => c :: l
    else c :: removeTags l
termination_by l => l.length

/-- Python's `str.isspace`: the Unicode White_Space characters and the
information separators U+001C–U+001F. -/
def isPySpace (c : Char) : Bool :=
  let n := c.toNat
  (0x09 ≤ n && n ≤ 0x0d) || (0x1c ≤ n && n ≤ 0x20) || n == 0x85 || n == 0xa0 ||
  n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200a) || n == 0x2028 || n == 0x2029 ||
  n == 0x202f || n == 0x205f || n == 0x3000

/-- Split on runs of whitespace, dropping empty fields (Python `str.split()`
with no separator). `cur` is the current word, reversed. -/
def wordsAux : List Char → List Char → List (List Char)
  | [], cur => if cur.isEmpty then [] else [cur.reverse]
  | c :: l, cur =>
    if isPySpace c then
      if cur.isEmpty then wordsAux l [] else cur.reverse :: wordsAux l []
    else wordsAux l (c :: cur)

/-- Python `str.split()` on a character list. -/
def words (l : List Char) : List (List Char) := wordsAux l []

/-- Pass 2 of `striptags`: `" ".join(value.split())`. -/
def collapseSpaces (l : List Char) : List Char := [' '].intercalate (words l)

/-! ### The executable passes

`removeTags`, `words` and `collapseSpaces` are stated on `List Char` and
recurse once per character. `removeTagsFast` reads the string in place
through a `Cursor`; `collapseFast` is one `String.foldl`. Both are proved
equal to their specifications, and `striptags_eq_fast` (`@[csimp]`) makes
`striptags` run them (and `unescapeFast`). -/

theorem take_eq_iff_isPrefixOf (d l : List Char) :
    (l.take d.length = d) ↔ d.isPrefixOf l = true := by
  induction d generalizing l with
  | nil => simp [List.isPrefixOf]
  | cons c cs ih =>
    cases l with
    | nil => simp [List.isPrefixOf]
    | cons x xs =>
      simp only [List.length_cons, List.take_succ_cons, List.cons.injEq, List.isPrefixOf,
        Bool.and_eq_true, beq_iff_eq, ← ih]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2⟩

/-- Where a tag or comment ends, given the text after its `<`. -/
def tagEndL (l : List Char) : Option (List Char) :=
  if l.take 3 = ['!', '-', '-'] then findCommentEnd (l.drop 3) else findClose l

theorem tagEndL_length {l r : List Char} (h : tagEndL l = some r) : r.length < l.length := by
  unfold tagEndL at h
  split at h
  · have := findCommentEnd_length h; simp at this; omega
  · exact findClose_length h

theorem removeTags_lt (l : List Char) :
    removeTags ('<' :: l) = match tagEndL l with
      | some r => removeTags r
      | none => '<' :: l := by
  rw [removeTags]
  simp only [ite_true, tagEndL]
  split
  · split <;> rename_i h1 <;> split <;> rename_i h2 <;> rw [h1] at h2 <;> cases h2 <;> rfl
  · split <;> rename_i h1 <;> split <;> rename_i h2 <;> rw [h1] at h2 <;> cases h2 <;> rfl

theorem removeTags_of_ne {c : Char} (l : List Char) (h : c ≠ '<') :
    removeTags (c :: l) = c :: removeTags l := by
  rw [removeTags]; simp [h]

namespace Cursor

variable {s : String.Slice}

/-- `findClose`, in place: the position after the first `>`. -/
def findCloseAt (p : s.Pos) : Option s.Pos :=
  if h : p = s.endPos then none
  else if p.get h = '>' then some (p.next h) else findCloseAt (p.next h)
termination_by (rest p).length
decreasing_by exact rest_next_length p h

/-- `findCommentEnd`, in place: the position after the first `-->`. -/
def findCommentEndAt (p : s.Pos) : Option s.Pos :=
  if h : p = s.endPos then none
  else if p.get h = '-' ∧ preW (p.next h) ['-', '>'] then some (advN (p.next h) 2)
  else findCommentEndAt (p.next h)
termination_by (rest p).length
decreasing_by exact rest_next_length p h

theorem findCloseAt_eq (p : s.Pos) : (findCloseAt p).map rest = findClose (rest p) := by
  induction p using rest_induction with
  | step p ih =>
    unfold findCloseAt
    split
    · subst_vars; simp [rest_endPos, findClose]
    · rename_i h
      rw [rest_next p h]
      simp only [findClose]
      by_cases hc : p.get h = '>'
      · simp [hc]
      · simp only [hc, ite_false]; exact ih _ (rest_next_length p h)

theorem findCommentEndAt_eq (p : s.Pos) :
    (findCommentEndAt p).map rest = findCommentEnd (rest p) := by
  induction p using rest_induction with
  | step p ih =>
    unfold findCommentEndAt
    split
    · subst_vars; simp [rest_endPos, findCommentEnd]
    · rename_i h
      rw [rest_next p h]
      simp only [findCommentEnd]
      have hpre : (preW (p.next h) ['-', '>'] = true) ↔ (rest (p.next h)).take 2 = ['-', '>'] := by
        rw [preW_eq]; exact (take_eq_iff_isPrefixOf ['-', '>'] _).symm
      by_cases hc : p.get h = '-' ∧ preW (p.next h) ['-', '>'] = true
      · rw [ite_eq_left hc, ite_eq_left ⟨hc.1, hpre.1 hc.2⟩]; simp [rest_advN]
      · rw [ite_eq_right hc, ite_eq_right (fun h' => hc ⟨h'.1, hpre.2 h'.2⟩)]
        exact ih _ (rest_next_length p h)

theorem findCloseAt_length {p q : s.Pos} (h : findCloseAt p = some q) :
    (rest q).length < (rest p).length := by
  have := findCloseAt_eq p; rw [h] at this
  exact findClose_length this.symm

theorem findCommentEndAt_length {p q : s.Pos} (h : findCommentEndAt p = some q) :
    (rest q).length < (rest p).length := by
  have := findCommentEndAt_eq p; rw [h] at this
  exact findCommentEnd_length this.symm

/-- Where the tag or comment whose `<` comes just before `q` ends, if it
does (the cursor form of `tagEndL`). -/
def tagEnd (q : s.Pos) : Option s.Pos :=
  if preW q ['!', '-', '-'] then findCommentEndAt (advN q 3) else findCloseAt q

theorem tagEnd_eq (q : s.Pos) : (tagEnd q).map rest = tagEndL (rest q) := by
  unfold tagEnd tagEndL
  have hpre : (preW q ['!', '-', '-'] = true) ↔ (rest q).take 3 = ['!', '-', '-'] := by
    rw [preW_eq]; exact (take_eq_iff_isPrefixOf ['!', '-', '-'] _).symm
  by_cases hp : preW q ['!', '-', '-'] = true
  · rw [ite_eq_left hp, ite_eq_left (hpre.1 hp), findCommentEndAt_eq, rest_advN]
  · rw [ite_eq_right hp, ite_eq_right (fun h' => hp (hpre.2 h')), findCloseAt_eq]

theorem tagEnd_length {q r : s.Pos} (h : tagEnd q = some r) :
    (rest r).length < (rest q).length := by
  have := tagEnd_eq q; rw [h] at this
  exact tagEndL_length this.symm

/-- `removeTags`, in place: append the text at `p` without its tags to `acc`. -/
def removeGo (p : s.Pos) (acc : String) : String :=
  if h : p = s.endPos then acc
  else if p.get h = '<' then
    match _hf : tagEnd (p.next h) with
    | some r => removeGo r acc
    | none => acc ++ copyRest p
  else removeGo (p.next h) (acc.push (p.get h))
termination_by (rest p).length
decreasing_by
  · have := tagEnd_length _hf
    have := rest_next_length p h
    omega
  · exact rest_next_length p h

theorem removeGo_eq (p : s.Pos) (acc : String) :
    (removeGo p acc).toList = acc.toList ++ removeTags (rest p) := by
  induction p using rest_induction generalizing acc with
  | step p ih =>
    rw [removeGo]
    split
    · subst_vars; simp [rest_endPos, removeTags]
    · rename_i h
      have hlt := rest_next_length p h
      split
      · rename_i hc
        have he := tagEnd_eq (p.next h)
        have hrest := rest_next p h
        rw [hc] at hrest
        rw [hrest, removeTags_lt]
        split
        · rename_i r hf
          rw [hf] at he; simp only [Option.map_some] at he
          rw [← he, ih r (by have := tagEnd_length hf; omega)]
        · rename_i hf
          rw [hf] at he; simp only [Option.map_none] at he
          rw [← he, String.toList_append, copyRest_toList, hrest]
      · rename_i hc
        rw [ih _ hlt, rest_next p h, removeTags_of_ne _ hc]
        simp [String.toList_push]

end Cursor

/-- `removeTags`, reading the string in place. -/
def removeTagsFast (t : String) : String := Cursor.removeGo t.toSlice.startPos ""

theorem removeTagsFast_toList (t : String) : (removeTagsFast t).toList = removeTags t.toList := by
  unfold removeTagsFast; rw [Cursor.removeGo_eq, Cursor.rest_startPos]; simp

/-- One character of `collapseSpaces`: the output so far, whether a word has
been written, and whether a space is owed before the next word. -/
def collapseStep (st : String × Bool × Bool) (c : Char) : String × Bool × Bool :=
  if isPySpace c then (st.1, st.2.1, st.2.1)
  else if st.2.2 then ((st.1.push ' ').push c, true, false)
  else (st.1.push c, true, false)

/-- `collapseSpaces`, as one fold into a `String`. -/
def collapseFast (t : String) : String := (t.foldl collapseStep ("", false, false)).1

theorem intercalate_snoc (sep : List Char) (xs : List (List Char)) (w : List Char) :
    sep.intercalate (xs ++ [w]) = if xs = [] then w else sep.intercalate xs ++ sep ++ w := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases xs with
    | nil => simp [List.intercalate_cons_cons]
    | cons y ys =>
      rw [List.cons_append, List.cons_append, List.intercalate_cons_cons, ← List.cons_append, ih,
        List.intercalate_cons_cons]
      simp

theorem collapse_fold (l cur : List Char) (prev : List (List Char)) (acc : String)
    (b q : Bool)
    (hacc : acc.toList = [' '].intercalate (prev ++ (if cur = [] then [] else [cur.reverse])))
    (hb : b = !(prev.isEmpty && cur.isEmpty))
    (hq : q = (cur.isEmpty && !prev.isEmpty)) :
    (l.foldl collapseStep (acc, b, q)).1.toList = [' '].intercalate (prev ++ wordsAux l cur) := by
  induction l generalizing cur prev acc b q with
  | nil =>
    simp only [List.foldl_nil, wordsAux, hacc]
    by_cases h : cur = [] <;> simp [h]
  | cons c l ih =>
    rw [List.foldl_cons, collapseStep]
    by_cases hs : isPySpace c
    · simp only [hs, ite_true, wordsAux]
      by_cases hc : cur = []
      · subst hc
        simp only [List.isEmpty_nil, ite_true]
        apply ih [] prev acc b b (by simpa using hacc) (by simp [hb]) (by simp [hb])
      · have hne : cur.isEmpty = false := by simpa using hc
        rw [ite_eq_right (by simpa using hc),
          show prev ++ cur.reverse :: wordsAux l [] = (prev ++ [cur.reverse]) ++ wordsAux l [] by simp]
        apply ih [] (prev ++ [cur.reverse]) acc b b (by simpa [hc] using hacc)
          (by simp [hb, hne]) (by simp [hb, hne])
    · simp only [hs, ite_false, Bool.false_eq_true, wordsAux]
      have key : ∀ acc' : String,
          acc'.toList = [' '].intercalate (prev ++ [(c :: cur).reverse]) →
          (l.foldl collapseStep (acc', true, false)).1.toList =
            [' '].intercalate (prev ++ wordsAux l (c :: cur)) :=
        fun acc' h => ih (c :: cur) prev acc' true false (by simpa using h) (by simp) (by simp)
      split
      · rename_i hq'
        apply key
        have hc : cur = [] := by subst hq; simp at hq'; exact hq'.1
        have hp : prev ≠ [] := by subst hq; simp at hq'; simpa using hq'.2
        subst hc
        simp only [ite_true, List.append_nil] at hacc
        simp [String.toList_push, hacc, intercalate_snoc, hp]
      · rename_i hq'
        apply key
        by_cases hc : cur = []
        · subst hc
          have hp : prev = [] := by subst hq; simpa using hq'
          subst hp
          simp at hacc; simp [hacc]
        · simp only [hc, ite_false] at hacc
          rw [String.toList_push, hacc, intercalate_snoc, intercalate_snoc]
          by_cases hp : prev = [] <;> simp [hp]

theorem collapseFast_toList (t : String) : (collapseFast t).toList = collapseSpaces t.toList := by
  unfold collapseFast collapseSpaces words
  rw [String.foldl_eq_foldl_toList]
  have := collapse_fold t.toList [] [] "" false false (by simp) (by simp) (by simp)
  simpa using this

/-- Remove tags and comments, normalise whitespace to single spaces, then
unescape (upstream `Markup.striptags`). The result is plain text. -/
def Markup.striptags (m : Markup) : String :=
  LeanMarkupsafe.unescape (String.ofList (collapseSpaces (removeTags m.str.toList)))

/-- `striptags`, with every pass run in place. -/
def Markup.striptagsFast (m : Markup) : String :=
  LeanMarkupsafe.unescape (collapseFast (removeTagsFast m.str))

/-- The executable `striptags` is `striptags`. -/
@[csimp] theorem Markup.striptags_eq_fast : @Markup.striptags = @Markup.striptagsFast := by
  funext m
  unfold Markup.striptags Markup.striptagsFast
  congr 1
  apply String.ext
  rw [collapseFast_toList, removeTagsFast_toList]
  simp

/-- Whitespace split (upstream `Markup.split()` / `rsplit()` with no
separator); each piece stays markup. -/
def Markup.split (m : Markup) : List Markup :=
  (words m.str.toList).map fun w => ⟨String.ofList w⟩

/-- One character of `split`: the words so far and the current word. -/
def splitStep (st : Array Markup × String) (c : Char) : Array Markup × String :=
  if isPySpace c then (if st.2.isEmpty then st else (st.1.push ⟨st.2⟩, ""))
  else (st.1, st.2.push c)

/-- The words after the last character. -/
def splitFinish (st : Array Markup × String) : List Markup :=
  (if st.2.isEmpty then st.1 else st.1.push ⟨st.2⟩).toList

/-- `split`, as one fold over the string (constant stack). -/
def Markup.splitFast (m : Markup) : List Markup := splitFinish (m.str.foldl splitStep (#[], ""))

theorem split_fold (l cur : List Char) (arr : Array Markup) :
    splitFinish (l.foldl splitStep (arr, String.ofList cur.reverse)) =
      arr.toList ++ (wordsAux l cur).map fun w => ⟨String.ofList w⟩ := by
  induction l generalizing cur arr with
  | nil =>
    simp only [List.foldl_nil, splitFinish, wordsAux]
    by_cases h : cur = [] <;> simp [h, String.isEmpty_iff]
  | cons c l ih =>
    rw [List.foldl_cons, splitStep]
    simp only [wordsAux]
    by_cases hs : isPySpace c
    · simp only [hs, ite_true]
      by_cases hc : cur = []
      · subst hc; simp only [List.reverse_nil, List.isEmpty_nil, ite_true]
        exact ih [] arr
      · have : (String.ofList cur.reverse).isEmpty = false := by
          simp [hc]
        simp only [this, Bool.false_eq_true, ite_false, List.isEmpty_iff, hc]
        have := ih [] (arr.push ⟨String.ofList cur.reverse⟩)
        simp only [List.reverse_nil] at this
        rw [show (String.ofList [] : String) = "" from rfl] at this
        rw [this]; simp
    · simp only [hs, Bool.false_eq_true, ite_false]
      have := ih (c :: cur) arr
      rw [← this]
      congr 3
      apply String.ext; simp [String.toList_push]

/-- The executable `split` is `split`. -/
@[csimp] theorem Markup.split_eq_fast : @Markup.split = @Markup.splitFast := by
  funext m
  unfold Markup.split Markup.splitFast words
  rw [String.foldl_eq_foldl_toList]
  have := split_fold m.str.toList [] #[]
  simpa using this.symm

end LeanMarkupsafe
