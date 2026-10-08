import BANANA.NonPrecompact.LinearBinarySMTree
import BANANA.NonPrecompact.BinarySubspaceRamseyInterface

/-!
# Linear ranges of exact binary successor approximations

An exact approximation of width d+1 records the action on binary words of
length d.  In the linear binary successor instance this action is an
injective linear map F₂^d -> F₂^N, where N is the exact terminal level.
This file packages its range as the FixedSubspace used by the BANANA
one-sided Ramsey interface.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

open Module

abbrev LinearBinaryH : SMTree binarySucc :=
  linearBinarySMTree

/-- A convenient all-zero word at one level. -/
def zeroAtLevel (n : ℕ) : AtLevel n :=
  ⟨⟨List.replicate n 0⟩, by simp⟩

/-- The common target level of a shape map on source level n. -/
def shapeTargetLevel
    (F : ShapeMap binarySucc) (n : ℕ) : ℕ :=
  (F (zeroAtLevel n).1).bits.length

theorem shapeTargetLevel_eq
    (F : ShapeMap binarySucc) (n : ℕ)
    (w : AtLevel n) :
    (F w.1).bits.length = shapeTargetLevel F n := by
  exact F.level_eq_of_level_eq (by
    change w.1.bits.length = (zeroAtLevel n).1.bits.length
    simp [w.2, zeroAtLevel])

/-- The linearity predicate carried by an M-map of the concrete instance. -/
theorem mmap_linear
    (F : SMTree.MMap LinearBinaryH) :
    LinearOnLevels F.map := by
  exact F.mem

/-- A canonical linear model for the action on one source level. -/
structure LevelLinearModel
    (F : SMTree.MMap LinearBinaryH) (n : ℕ) where
  map :
    (Fin n → F2) →ₗ[F2]
      (Fin (shapeTargetLevel F.map n) → F2)
  action :
    ∀ w : AtLevel n,
      ∃ hFw :
          (F w.1).bits.length =
            shapeTargetLevel F.map n,
        levelEquiv (shapeTargetLevel F.map n)
            ⟨F w.1, hFw⟩ =
          map (levelEquiv n w)

noncomputable def levelLinearModel
    (F : SMTree.MMap LinearBinaryH) (n : ℕ) :
    LevelLinearModel F n := by
  classical
  let m := Classical.choose (mmap_linear F n)
  have hExist := Classical.choose_spec (mmap_linear F n)
  let φ := Classical.choose hExist
  have hφ := Classical.choose_spec hExist
  have hm : m = shapeTargetLevel F.map n := by
    obtain ⟨h0, _⟩ := hφ (zeroAtLevel n)
    exact h0.symm
  rcases hm with rfl
  exact ⟨φ, hφ⟩

theorem levelLinearModel_injective
    (F : SMTree.MMap LinearBinaryH) (n : ℕ) :
    Function.Injective (levelLinearModel F n).map :=
  levelWitness_injective
    F.map (levelLinearModel F n).map
    (levelLinearModel F n).action

/-- For an exact approximation, its representative's target level on source
level d is the specified terminal level N. -/
theorem exact_shapeTargetLevel
    {d N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (d + 1) N) :
    shapeTargetLevel
        (f.1.representative LinearBinaryH).map d = N := by
  let R := f.1.representative LinearBinaryH
  have hlevel :
      LinearBinaryH.levelMap R.map d =
        shapeTargetLevel R.map d := by
    let w := zeroAtLevel d
    have h :=
      LinearBinaryH.levelMap_eq R.map (a := w.1)
    change
      LinearBinaryH.levelMap R.map w.1.bits.length =
        (R w.1).bits.length at h
    have hw : w.1.bits.length = d := w.2
    rw [hw] at h
    simpa [shapeTargetLevel, w] using h
  have hterm : LinearBinaryH.levelMap R.map d = N := by
    have ht := f.2
    change
      LinearBinaryH.levelMap
        (f.1.representative LinearBinaryH).map
        (0 + (d + 1) - 1) = N at ht
    simpa [R] using ht
  exact hlevel.symm.trans hterm

/-- Linear top-level model of an exact finite approximation. -/
structure ExactLinearModel
    {d N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (d + 1) N) where
  map : (Fin d → F2) →ₗ[F2] (Fin N → F2)
  action :
    ∀ w : AtLevel d,
      ∃ hFw :
          ((f.1.representative LinearBinaryH) w.1).bits.length = N,
        levelEquiv N
            ⟨(f.1.representative LinearBinaryH) w.1, hFw⟩ =
          map (levelEquiv d w)

/-- A level-linear action packaged with an independently specified
target dimension. The map and its action law must be transported together
when the target dimension is changed. -/
private structure LevelModelAt
    (R : SMTree.MMap LinearBinaryH) (d N : ℕ) where
  map : (Fin d → F2) →ₗ[F2] (Fin N → F2)
  action :
    ∀ w : AtLevel d,
      ∃ hRw : (R w.1).bits.length = N,
        levelEquiv N ⟨R w.1, hRw⟩ =
          map (levelEquiv d w)

private noncomputable def levelModelAt_of_target
    (R : SMTree.MMap LinearBinaryH) (d N : ℕ)
    (hN : shapeTargetLevel R.map d = N) :
    LevelModelAt R d N := by
  cases hN
  exact ⟨(levelLinearModel R d).map,
    (levelLinearModel R d).action⟩

noncomputable def exactLinearModel
    {d N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (d + 1) N) :
    ExactLinearModel f := by
  let R := f.1.representative LinearBinaryH
  let M : LevelModelAt R d N :=
    levelModelAt_of_target R d N (exact_shapeTargetLevel f)
  exact ⟨M.map, M.action⟩

theorem exactLinearModel_injective
    {d N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (d + 1) N) :
    Function.Injective (exactLinearModel f).map :=
  levelWitness_injective
    (f.1.representative LinearBinaryH).map
    (exactLinearModel f).map
    (exactLinearModel f).action

/-- The d-dimensional subspace represented by an exact finite successor
approximation ending at level N. -/
noncomputable def exactSubspace
    {d N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (d + 1) N) :
    FixedSubspace d N := by
  let E := (exactLinearModel f).map
  refine ⟨LinearMap.range E, ?_⟩
  rw [LinearMap.finrank_range_of_inj
    (exactLinearModel_injective f)]
  simp [Module.finrank_fintype_fun_eq_card]


/-- To identify the subspace of an exact successor approximation, it
suffices to prove containment in another subspace of the same
dimension. This avoids a separate surjectivity argument in both
inductive coordinate-extension cases. -/
theorem exactSubspace_eq_of_range_le
    {d N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (d + 1) N)
    (P : FixedSubspace d N)
    (hle : (exactSubspace f).1 ≤ P.1) :
    exactSubspace f = P := by
  apply Subtype.ext
  exact Submodule.eq_of_le_of_finrank_eq hle
    ((exactSubspace f).2.trans P.2.symm)

/-- It is enough to check containment on the images of the words at
the last source level, using the linear action of the representative.
No choice of basis of the image subspace is required. -/
theorem exactSubspace_eq_of_action_mem
    {d N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (d + 1) N)
    (P : FixedSubspace d N)
    (hmem : ∀ (w : AtLevel d)
        (hFw : ((f.1.representative LinearBinaryH) w.1).bits.length = N),
        levelEquiv N
            ⟨(f.1.representative LinearBinaryH) w.1, hFw⟩ ∈ P.1) :
    exactSubspace f = P := by
  apply exactSubspace_eq_of_range_le f P
  rintro v ⟨x, rfl⟩
  let w : AtLevel d := (levelEquiv d).symm x
  obtain ⟨hFw, hw⟩ := (exactLinearModel f).action w
  have hx : levelEquiv d w = x :=
    (levelEquiv d).apply_symm_apply x
  have h := hmem w hFw
  rw [hw, hx] at h
  exact h

end BinaryWord
end SuccessorTree.NonPrecompact
