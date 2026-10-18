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

/-- Remove tags and comments, normalise whitespace to single spaces, then
unescape (upstream `Markup.striptags`). The result is plain text. -/
def Markup.striptags (m : Markup) : String :=
  LeanMarkupsafe.unescape (String.ofList (collapseSpaces (removeTags m.str.toList)))

/-- Whitespace split (upstream `Markup.split()` / `rsplit()` with no
separator); each piece stays markup. -/
def Markup.split (m : Markup) : List Markup :=
  (words m.str.toList).map fun w => ⟨String.ofList w⟩

end LeanMarkupsafe
