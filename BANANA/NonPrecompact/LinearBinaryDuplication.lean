import BANANA.NonPrecompact.LinearBinaryMonoidBasic

/-!
# Duplication for the linear binary successor monoid

For source level `n < m`, duplicate the incoming edge at level `m` by
inserting the linear coordinate which is the projection to source coordinate
`n`.  This is exactly the duplication argument in the manuscript's finite
linear successor-tree application.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

/-- M3 for the set of levelwise-linear binary prefix-tree shape maps. -/
theorem linearOnLevels_m3 :
    ∀ (n m : ℕ), n < m →
      ∃ D : ShapeMap binarySucc,
        LinearOnLevels D ∧
        D.SkipsOnly m ∧
        ∀ (a b : BinaryWord) (p : List BinaryWord) (c : F2)
          (s : BinaryWord),
          LevelTree.lev a = n →
          LevelTree.lev b = m →
          binarySucc.succ a p c = some s →
          s ≤ b →
          binarySucc.succ b p c = some (D b) := by
  intro n m hnm
  let D : ShapeMap binarySucc :=
    insertLinearCoordinateShapeMap m (coordinateRule n m hnm)
  refine ⟨D,
    linearOnLevels_insertLinearCoordinateShapeMap
      m (coordinateRule n m hnm),
    insertLinearCoordinateShapeMap_skipsOnly
      m (coordinateRule n m hnm),
    ?_⟩
  intro a b p c s ha hb hs hsb
  have hp : p = [] := by
    by_contra hp
    change
      (if p = [] then some (appendBit a c) else none) =
        some s at hs
    simp [hp] at hs
  subst p
  have hs_eq : s = appendBit a c := by
    change
      (if ([] : List BinaryWord) = [] then
          some (appendBit a c) else none) = some s at hs
    simpa using hs.symm
  subst s
  have ha' : a.bits.length = n := ha
  have hb' : b.bits.length = m := hb
  have hDb :
      D b = appendBit b c := by
    exact insert_coordinateRule_of_edge
      hnm ha' hb' hsb
  change
    (if ([] : List BinaryWord) = [] then
        some (appendBit b c) else none) = some (D b)
  simp [hDb]

end BinaryWord
end SuccessorTree.NonPrecompact
