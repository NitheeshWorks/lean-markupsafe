/-!
# A cursor over a string

The specifications read their input as a `List Char`: the right shape for
proofs, the wrong one for a 20 MB string, since a list costs 24 bytes a
character and the specification functions recurse once per character. The
executable versions (`unescapeFast`, `removeTagsFast`, the fast format
engines) read the same input in place, through positions of a
`String.Slice`, and build their output in a `String`; this file is their
vocabulary.

`rest p` is the list the specification would see at `p`. It appears only in
proofs and termination measures and is never computed at run time.
Every walker here is tail recursive (constant stack).
-/

namespace LeanMarkupsafe

open String

namespace Cursor

variable {s : Slice}

/-- The characters from `p` to the end of the slice: the specification's view
of the input at `p`. -/
def rest (p : s.Pos) : List Char := (s.sliceFrom p).copy.toList

theorem rest_endPos : rest s.endPos = [] := by
  have h := Slice.Pos.splits s.endPos
  have h3 := h.eq_right (Slice.splits_endPos s)
  simp [rest, h3]

theorem rest_next (p : s.Pos) (h : p ≠ s.endPos) : rest p = p.get h :: rest (p.next h) := by
  have h1 := Slice.Pos.splits_next_right p h
  have h2 := h1.eq_right (Slice.Pos.splits p)
  simp [rest, ← h2]

theorem rest_startPos : rest s.startPos = s.copy.toList := by
  simp [rest]

theorem rest_next_length (p : s.Pos) (h : p ≠ s.endPos) :
    (rest (p.next h)).length < (rest p).length := by
  rw [rest_next p h]; simp

theorem rest_eq_nil_iff (p : s.Pos) : rest p = [] ↔ p = s.endPos := by
  constructor
  · intro hp
    by_cases h : p = s.endPos
    · exact h
    · rw [rest_next p h] at hp; cases hp
  · rintro rfl; exact rest_endPos

/-- The character at `p`, if any. -/
def peek (p : s.Pos) : Option Char := if h : p = s.endPos then none else some (p.get h)

/-- One character on (stays put at the end). -/
def adv (p : s.Pos) : s.Pos := if h : p = s.endPos then p else p.next h

/-- `n` characters on (stops at the end). -/
def advN (p : s.Pos) : Nat → s.Pos
  | 0 => p
  | n + 1 => advN (adv p) n

/-- `d` is a prefix of the text at `p`. -/
def preW (p : s.Pos) : List Char → Bool
  | [] => true
  | c :: cs => peek p == some c && preW (adv p) cs

/-- Everything from `p` on, as a string (copied in one piece). -/
def copyRest (p : s.Pos) : String := (s.sliceFrom p).copy

/-! ## The walkers agree with the list view -/

theorem peek_eq (p : s.Pos) : peek p = (rest p).head? := by
  unfold peek
  split
  · subst_vars; simp [rest_endPos]
  · rename_i h; rw [rest_next p h]; rfl

theorem rest_adv (p : s.Pos) : rest (adv p) = (rest p).tail := by
  unfold adv
  split
  · subst_vars; simp [rest_endPos]
  · rename_i h; rw [rest_next p h]; rfl

theorem rest_advN (p : s.Pos) (n : Nat) : rest (advN p n) = (rest p).drop n := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp only [advN, ih, rest_adv]; cases rest p <;> simp

theorem preW_eq (p : s.Pos) (d : List Char) : preW p d = d.isPrefixOf (rest p) := by
  induction d generalizing p with
  | nil => simp [preW]
  | cons c cs ih =>
    simp only [preW, ih, peek_eq, rest_adv]
    cases rest p <;> simp [List.isPrefixOf, Bool.beq_comm]

theorem copyRest_toList (p : s.Pos) : (copyRest p).toList = rest p := rfl

/-- Strong induction on the length of the text left at a position. -/
theorem rest_induction {P : s.Pos → Prop}
    (step : ∀ p, (∀ q, (rest q).length < (rest p).length → P q) → P p) (p : s.Pos) : P p := by
  have key : ∀ n, ∀ p : s.Pos, (rest p).length ≤ n → P p := by
    intro n
    induction n with
    | zero => intro p hp; exact step p (fun q hq => by omega)
    | succ n ih => intro p hp; exact step p (fun q hq => ih q (by omega))
  exact key _ p (Nat.le_refl _)

end Cursor

end LeanMarkupsafe
