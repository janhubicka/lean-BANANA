import BANANA.NonPrecompact.SymplecticAlternatingBilinPreservation

/-!
# Coordinate-change form of the alternating strong amalgam

Given *arbitrary finite original vector-space carriers* VA, VB, VC
and F₂-linear coordinate equivalences eA, eB, eC which carry the
two embeddings of VA to the standard shared A-block inclusions,
the zero-cross block construction produces a strong amalgam back
on the original carriers. The native maps into the amalgam are
compositions of the coordinate equivalences with the two canonical
linear inclusions.

The statement checks equality of images on the whole vector
spaces, not just on bases, and preservation of the original
transported bilinear forms on all vector pairs.

It does NOT claim that the required compatible equivalences always
exist. That common-basis extension argument is the remaining
arbitrary-embedding obligation for the full Fraïssé AP theorem.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Conditional arbitrary-carrier strong amalgamation: given bases
adapted to the embeddings of a common VA, produce two linear maps
which preserve the original coordinate-transported pairings and
intersect precisely on the original embedded VA.

No perfectness or nondegeneracy is assumed, so the result applies
to degenerate alternating forms, including the zero space. -/
theorem symplecticAlternating_strongAmalgam_of_compatibleCoordinates
    {VA VB VC A X Y : Type*}
    [AddCommGroup VA] [Module F2 VA]
    [AddCommGroup VB] [Module F2 VB]
    [AddCommGroup VC] [Module F2 VC]
    [Fintype A] [Fintype X] [Fintype Y]
    (eA : VA ≃ₗ[F2] (A → F2))
    (eB : VB ≃ₗ[F2] (Sum A X → F2))
    (eC : VC ≃ₗ[F2] (Sum A Y → F2))
    (iB : VA →ₗ[F2] VB) (iC : VA →ₗ[F2] VC)
    (hBbase : ∀ a, eB (iB a) =
      symplecticBlockVectorCommonLeft (eA a))
    (hCbase : ∀ a, eC (iC a) =
      symplecticBlockVectorCommonRight (eA a))
    (B : Matrix (Sum A X) (Sum A X) F2)
    (C : Matrix (Sum A Y) (Sum A Y) F2)
    (hcommon : ∀ a a',
      B (.inl a) (.inl a') = C (.inl a) (.inl a'))
    (hBdiag : ∀ i, B i i = 0)
    (hCdiag : ∀ i, C i i = 0)
    (hBsymm : ∀ i j, B i j = B j i)
    (hCsymm : ∀ i j, C i j = C j i) :
    ∃ (D : Matrix (Sum A (Sum X Y)) (Sum A (Sum X Y)) F2)
      (fB : VB →ₗ[F2] (Sum A (Sum X Y) → F2))
      (fC : VC →ₗ[F2] (Sum A (Sum X Y) → F2)),
      (∀ i, D i i = 0) ∧
      (∀ i j, D i j = D j i) ∧
      Function.Injective fB ∧
      Function.Injective fC ∧
      (∀ u v, fB u = fC v ↔
        ∃ a : VA, u = iB a ∧ v = iC a) ∧
      (∀ u v : VB,
        (Matrix.toBilin' D) (fB u) (fB v) =
          (Matrix.toBilin' B) (eB u) (eB v)) ∧
      (∀ u v : VC,
        (Matrix.toBilin' D) (fC u) (fC v) =
          (Matrix.toBilin' C) (eC u) (eC v)) := by
  classical
  refine ⟨symplecticBlockAmalgam B C,
    symplecticBlockVectorLeft.comp eB.toLinearMap,
    symplecticBlockVectorRight.comp eC.toLinearMap,
    symplecticBlockAmalgam_diag_zero B C hBdiag hCdiag,
    symplecticBlockAmalgam_symmetric B C hBsymm hCsymm,
    symplecticBlockVectorLeft_injective.comp eB.injective,
    symplecticBlockVectorRight_injective.comp eC.injective,
    ?_, ?_, ?_⟩
  · intro u v
    change symplecticBlockVectorLeft (eB u) =
      symplecticBlockVectorRight (eC v) ↔
      ∃ a : VA, u = iB a ∧ v = iC a
    constructor
    · intro h
      obtain ⟨w, hwB, hwC⟩ :=
        (symplecticBlockVector_intersection (eB u) (eC v)).mp h
      refine ⟨eA.symm w, ?_, ?_⟩
      · apply eB.injective
        calc
          eB u = symplecticBlockVectorCommonLeft w := hwB
          _ = symplecticBlockVectorCommonLeft (eA (eA.symm w)) := by simp
          _ = eB (iB (eA.symm w)) := (hBbase _).symm
      · apply eC.injective
        calc
          eC v = symplecticBlockVectorCommonRight w := hwC
          _ = symplecticBlockVectorCommonRight (eA (eA.symm w)) := by simp
          _ = eC (iC (eA.symm w)) := (hCbase _).symm
    · rintro ⟨a, rfl, rfl⟩
      rw [hBbase, hCbase]
      exact (symplecticBlockVector_intersection _ _).mpr
        ⟨eA a, rfl, rfl⟩
  · intro u v
    change (Matrix.toBilin' (symplecticBlockAmalgam B C))
        (symplecticBlockVectorLeft (eB u))
        (symplecticBlockVectorLeft (eB v)) =
        (Matrix.toBilin' B) (eB u) (eB v)
    exact symplecticBlockVectorLeft_pairing B C (eB u) (eB v)
  · intro u v
    change (Matrix.toBilin' (symplecticBlockAmalgam B C))
        (symplecticBlockVectorRight (eC u))
        (symplecticBlockVectorRight (eC v)) =
        (Matrix.toBilin' C) (eC u) (eC v)
    exact symplecticBlockVectorRight_pairing B C hcommon (eC u) (eC v)

end SuccessorTree.NonPrecompact
