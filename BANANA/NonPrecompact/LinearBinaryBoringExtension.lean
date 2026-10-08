import BANANA.NonPrecompact.LinearBinaryComposition
import BANANA.NonPrecompact.LinearBinaryExactCoordinates
import BANANA.NonPrecompact.BinarySubspaceStep

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

/-- The exact insertion has exactly the expected linear action:
inserting the final coordinate `e(x)` at the end of `x`. -/
theorem finalLinearInsertionExact_model_eq
    (N : ℕ) (e : LinearBoringRule N) :
    (exactLinearModel (finalLinearInsertionExact N e)).map =
      insertBoringLinearMap N N le_rfl e := by
  apply LinearMap.ext
  intro x
  let w : AtLevel N := (levelEquiv N).symm x
  have hw : levelEquiv N w = x :=
    (levelEquiv N).apply_symm_apply x
  obtain ⟨hFw, haction⟩ :=
    (exactLinearModel (finalLinearInsertionExact N e)).action w
  let F := finalLinearInsertion N e
  have hfix : F.FixesBelow LinearBinaryH 0 := by
    intro y hy
    omega
  have hrep :
      ((finalLinearInsertionExact N e).1.representative LinearBinaryH) w.1 =
        F w.1 := by
    change
      ((F.toAM LinearBinaryH 0 (N + 1) hfix).representative
        LinearBinaryH) w.1 = F w.1
    apply SMTree.MMap.toAM_representative_agrees
      LinearBinaryH F 0 (N + 1) hfix
    change w.1.bits.length < N + 1
    omega
  have hlen :
      (insertLinearCoordinate N e w.1).bits.length = N + 1 := by
    rw [length_insertLinearCoordinate]
    simp [w.2]
  have hsub :
      (⟨((finalLinearInsertionExact N e).1.representative
            LinearBinaryH) w.1, hFw⟩ : AtLevel (N + 1)) =
        (⟨insertLinearCoordinate N e w.1, hlen⟩ : AtLevel (N + 1)) :=
    Subtype.ext hrep
  calc
    (exactLinearModel (finalLinearInsertionExact N e)).map x =
        (exactLinearModel (finalLinearInsertionExact N e)).map
          (levelEquiv N w) := by rw [hw]
    _ = levelEquiv (N + 1)
          ⟨((finalLinearInsertionExact N e).1.representative
              LinearBinaryH) w.1, hFw⟩ := haction.symm
    _ = levelEquiv (N + 1)
          ⟨insertLinearCoordinate N e w.1, hlen⟩ :=
      congrArg (levelEquiv (N + 1)) hsub
    _ = insertBoringLinearMap N N le_rfl e (levelEquiv N w) :=
      levelEquiv_insertLinearCoordinate N N le_rfl e w
    _ = insertBoringLinearMap N N le_rfl e x := by rw [hw]

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


/-- On finite coordinate vectors, the final boring insertion is simply
the operation `x ↦ (x,e(x))`. -/
theorem finalLinearInsertion_linear_apply
    (N : ℕ) (e : LinearBoringRule N) (x : Fin N → F2) :
    insertBoringLinearMap N N le_rfl e x = Fin.snoc x (e x) := by
  have hprefix :
      prefixRestrictionLinearMap N N le_rfl x = x := by
    funext i
    rfl
  change (Fin.last N).insertNth
      (e (prefixRestrictionLinearMap N N le_rfl x)) x =
        Fin.snoc x (e x)
  rw [hprefix]
  exact Fin.insertNth_last' (e x) x

/-- The last-coordinate equivalence recovers both the old vector and
the inserted linear functional. -/
theorem lastCoordinateLinearEquiv_insertion
    (N : ℕ) (e : LinearBoringRule N) (x : Fin N → F2) :
    lastCoordinateLinearEquiv N
        (insertBoringLinearMap N N le_rfl e x) = (x, e x) := by
  rw [finalLinearInsertion_linear_apply]
  simp [lastCoordinateLinearEquiv]

/-- Subspace membership after inserting a dependent coordinate is
exactly the graph condition over the original subspace. -/
theorem mem_finalLinearInsertion_map_iff
    (N : ℕ) (e : LinearBoringRule N)
    (Q : Submodule F2 (Fin N → F2))
    (z : Fin (N + 1) → F2) :
    z ∈ Submodule.map (insertBoringLinearMap N N le_rfl e) Q ↔
      (lastCoordinateLinearEquiv N z).1 ∈ Q ∧
      (lastCoordinateLinearEquiv N z).2 =
        e (lastCoordinateLinearEquiv N z).1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [lastCoordinateLinearEquiv_insertion]
    exact ⟨hx, rfl⟩
  · intro hz
    let x : Fin N → F2 := (lastCoordinateLinearEquiv N z).1
    have hzEq : z = insertBoringLinearMap N N le_rfl e x := by
      apply (lastCoordinateLinearEquiv N).injective
      rw [lastCoordinateLinearEquiv_insertion]
      apply Prod.ext
      · rfl
      · exact hz.2
    rw [hzEq]
    exact ⟨x, hz.1, rfl⟩

/-- The exact-dependent-coordinate subspace range is explicitly the
image under the final linear insertion. -/
theorem extendExactWithBoring_range_explicit
    {d N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (d + 1) N)
    (e : LinearBoringRule N) :
    (exactSubspace (extendExactWithBoring f e)).1 =
      Submodule.map (insertBoringLinearMap N N le_rfl e)
        (exactSubspace f).1 := by
  rw [extendExactWithBoring_range,
    finalLinearInsertionExact_model_eq]

/-- A dependent-coordinate extension realises any fixed-dimensional
subspace given by the graph of a linear functional over its old range.
This is the exact form needed by the ambient-dimension induction. -/
theorem extendExactWithBoring_realises_graph
    {d N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (d + 1) N)
    (e : LinearBoringRule N)
    (P : FixedSubspace d (N + 1))
    (hgraph : ∀ z : Fin (N + 1) → F2,
      z ∈ P.1 ↔
        (lastCoordinateLinearEquiv N z).1 ∈ (exactSubspace f).1 ∧
        (lastCoordinateLinearEquiv N z).2 =
          e (lastCoordinateLinearEquiv N z).1) :
    exactSubspace (extendExactWithBoring f e) = P := by
  apply Subtype.ext
  apply Submodule.ext
  intro z
  rw [extendExactWithBoring_range_explicit]
  exact (mem_finalLinearInsertion_map_iff N e (exactSubspace f).1 z).trans
    (hgraph z).symm

end BinaryWord
end SuccessorTree.NonPrecompact
