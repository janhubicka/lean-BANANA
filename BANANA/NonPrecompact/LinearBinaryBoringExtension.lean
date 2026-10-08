import BANANA.NonPrecompact.LinearBinaryComposition
import BANANA.NonPrecompact.LinearBinaryExactCoordinates

/-!
# Exact extension by a dependent binary coordinate

A linear boring-coordinate insertion at the end of the current target
word is itself a finite exact successor approximation of width `N+1`
and terminal level `N+1`. Hence its composition with an exact
approximation ending at level `N` extends the latter by one dependent
coordinate. The exact-composition range theorem can then calculate the
resulting subspace without a second manual composition argument.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

open Module

/-- The distinguished total map inserting the value of a linear
functional at the last target coordinate. -/
def finalLinearInsertion (N : ℕ) (e : LinearBoringRule N) :
    SMTree.MMap LinearBinaryH :=
  ⟨insertLinearCoordinateShapeMap N e,
    linearOnLevels_insertLinearCoordinateShapeMap N e⟩

/-- The final-coordinate insertion takes source level `N` to `N+1`. -/
theorem finalLinearInsertion_levelMap
    (N : ℕ) (e : LinearBoringRule N) :
    LinearBinaryH.levelMap (finalLinearInsertion N e).map N = N + 1 := by
  let w := zeroAtLevel N
  have hw : LevelTree.lev w.1 = N := w.2
  have hlevel :=
    LinearBinaryH.levelMap_eq
      (finalLinearInsertion N e).map (a := w.1)
  rw [hw] at hlevel
  have hins :=
    insertLinearCoordinateShapeMap_level N e w.1
  change LevelTree.lev ((finalLinearInsertion N e) w.1) =
      (if LevelTree.lev w.1 < N then
          LevelTree.lev w.1
       else LevelTree.lev w.1 + 1) at hins
  rw [hw] at hins
  simp only [lt_irrefl, ↓reduceIte] at hins
  exact hlevel.trans hins

/-- The exact finite approximation whose top-level action inserts
the final coordinate `e(x)`. -/
noncomputable def finalLinearInsertionExact
    (N : ℕ) (e : LinearBoringRule N) :
    SMTree.AM.At LinearBinaryH 0 (N + 1) (N + 1) := by
  let F := finalLinearInsertion N e
  have hfix : F.FixesBelow LinearBinaryH 0 := by
    intro x hx
    omega
  let f : SMTree.AM LinearBinaryH 0 (N + 1) :=
    F.toAM LinearBinaryH 0 (N + 1) hfix
  refine ⟨f, ?_⟩
  have hterm :=
    SMTree.MMap.toAM_terminalLevel LinearBinaryH F 0 (N + 1)
      hfix (by omega)
  change f.terminalLevel LinearBinaryH = N + 1
  rw [hterm]
  have hlast : 0 + (N + 1) - 1 = N := by omega
  rw [hlast]
  exact finalLinearInsertion_levelMap N e

/-- Adding the dependent coordinate to an exact approximation is
exact finite composition with the insertion approximation. -/
noncomputable def extendExactWithBoring
    {d N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (d + 1) N)
    (e : LinearBoringRule N) :
    SMTree.AM.At LinearBinaryH 0 (d + 1) (N + 1) :=
  SMTree.exactComp LinearBinaryH
    (by omega : 0 < N + 1) (by omega : 0 < d + 1)
    (finalLinearInsertionExact N e) f

/-- The range of the dependent-coordinate extension is the image of
the preceding exact subspace under the inserted-coordinate map.
This is an instance of the exact-composition theorem. -/
theorem extendExactWithBoring_range
    {d N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (d + 1) N)
    (e : LinearBoringRule N) :
    (exactSubspace (extendExactWithBoring f e)).1 =
      Submodule.map
        (exactLinearModel (finalLinearInsertionExact N e)).map
        (exactSubspace f).1 := by
  exact exactSubspace_comp (finalLinearInsertionExact N e) f

end BinaryWord
end SuccessorTree.NonPrecompact
