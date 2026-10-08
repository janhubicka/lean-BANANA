import BANANA.NonPrecompact.BinaryWordTree
import Mathlib.Data.List.InsertIdx

/-!
# Linear boring coordinate insertions on binary words

A boring coordinate at position `m` is a linear functional of the previous
`m` coordinates.  Inserting such a coordinate is the basic operation behind
both M2 and M3 for the vector-space successor-tree instance.

This file keeps the operation at the finite-word level.  The next layer
packages it as a shape-preserving map and then as an element of the linear
monoid.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

/-- A linear rule for a coordinate inserted after a prefix of length `m`. -/
abbrev LinearBoringRule (m : ℕ) :=
  (Fin m → F2) →ₗ[F2] F2

/-- The first `m` coordinates of a word known to have length at least `m`. -/
def prefixCoords
    (w : BinaryWord) (m : ℕ) (h : m ≤ w.bits.length) :
    Fin m → F2 :=
  fun i => w.bits.get
    ⟨i.1, lt_of_lt_of_le i.2 h⟩

/-- Insert the value of a linear boring rule at coordinate `m`.
Words shorter than `m` are unchanged. -/
def insertLinearCoordinate
    (m : ℕ) (e : LinearBoringRule m) (w : BinaryWord) : BinaryWord :=
  if h : m ≤ w.bits.length then
    ⟨w.bits.insertIdx m (e (prefixCoords w m h))⟩
  else
    w

theorem insertLinearCoordinate_of_lt
    (m : ℕ) (e : LinearBoringRule m) (w : BinaryWord)
    (h : w.bits.length < m) :
    insertLinearCoordinate m e w = w := by
  simp [insertLinearCoordinate, Nat.not_le.mpr h]

theorem insertLinearCoordinate_of_le
    (m : ℕ) (e : LinearBoringRule m) (w : BinaryWord)
    (h : m ≤ w.bits.length) :
    (insertLinearCoordinate m e w).bits =
      w.bits.insertIdx m (e (prefixCoords w m h)) := by
  simp [insertLinearCoordinate, h]

theorem length_insertLinearCoordinate
    (m : ℕ) (e : LinearBoringRule m) (w : BinaryWord) :
    (insertLinearCoordinate m e w).bits.length =
      if m ≤ w.bits.length then w.bits.length + 1 else w.bits.length := by
  by_cases h : m ≤ w.bits.length
  · simp [insertLinearCoordinate, h,
      List.length_insertIdx_of_le_length h]
  · simp [insertLinearCoordinate, h]

/-- Erasing the inserted coordinate recovers the original word. -/
theorem eraseIdx_insertLinearCoordinate
    (m : ℕ) (e : LinearBoringRule m) (w : BinaryWord)
    (h : m ≤ w.bits.length) :
    (insertLinearCoordinate m e w).bits.eraseIdx m = w.bits := by
  rw [insertLinearCoordinate_of_le m e w h]
  exact List.eraseIdx_insertIdx_self ..

/-- Linear-coordinate insertion is injective even though the inserted value
depends on the input prefix. -/
theorem insertLinearCoordinate_injective
    (m : ℕ) (e : LinearBoringRule m) :
    Function.Injective (insertLinearCoordinate m e) := by
  intro x y hxy
  have hlen :=
    congrArg (fun z : BinaryWord => z.bits.length) hxy
  rw [length_insertLinearCoordinate,
    length_insertLinearCoordinate] at hlen
  by_cases hx : m ≤ x.bits.length
  · have hy : m ≤ y.bits.length := by
      by_contra hy
      simp [hx, hy] at hlen
      omega
    have hbits := congrArg BinaryWord.bits hxy
    have herase :=
      congrArg (fun l : List F2 => l.eraseIdx m) hbits
    apply BinaryWord.ext
    simpa [eraseIdx_insertLinearCoordinate m e x hx,
      eraseIdx_insertLinearCoordinate m e y hy] using herase
  · have hy : ¬ m ≤ y.bits.length := by
      by_contra hy
      simp [hx, hy] at hlen
      omega
    simpa [insertLinearCoordinate, hx, hy] using hxy

end BinaryWord
end SuccessorTree.NonPrecompact
