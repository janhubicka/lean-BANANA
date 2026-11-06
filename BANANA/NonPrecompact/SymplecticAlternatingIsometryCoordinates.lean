import BANANA.NonPrecompact.SymplecticAlternatingMatrixCertificate

/-!
# Isometric embeddings in compatible coordinates give a common matrix block

The original finite alternating spaces are allowed to be degenerate.
The preceding adapted-coordinate theorem makes the two embeddings of
the common space standard A-block inclusions, using ordinary vector
complements. This module transports each original bilinear form to
its coordinate matrix and verifies that the two A-by-A blocks agree.

There is no assumption of an orthogonal complement or nondegeneracy.
Everything here is independent of the later copy-Ramsey category API.

DRAFT / NOT KERNEL VERIFIED.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- The common subspace inclusion on the left maps a single
coordinate vector to the corresponding single ambient coordinate. -/
theorem symplecticCommonLeft_single
    {A X : Type*} (a : A) :
    symplecticBlockVectorCommonLeft (A := A) (X := X)
      (Pi.single a (1 : F2)) =
        Pi.single (Sum.inl a) (1 : F2) := by
  classical
  funext k
  cases k with
  | inl b => simp [symplecticBlockVectorCommonLeft, Pi.single_apply]
  | inr x => simp [symplecticBlockVectorCommonLeft, Pi.single_apply]

/-- Corresponding right inclusion. -/
theorem symplecticCommonRight_single
    {A Y : Type*} (a : A) :
    symplecticBlockVectorCommonRight (A := A) (Y := Y)
      (Pi.single a (1 : F2)) =
        Pi.single (Sum.inl a) (1 : F2) := by
  classical
  funext k
  cases k with
  | inl b => simp [symplecticBlockVectorCommonRight, Pi.single_apply]
  | inr y => simp [symplecticBlockVectorCommonRight, Pi.single_apply]

/-- Coefficient matrix of a bilinear form after an arbitrary
linear coordinate equivalence. No orthogonality assumptions. -/
noncomputable def symplecticFormTransportMatrix
    {V I : Type*}
    [AddCommGroup V] [Module F2 V] [Fintype I]
    (β : LinearMap.BilinForm F2 V)
    (e : V ≃ₗ[F2] (I → F2)) : Matrix I I F2 :=
  LinearMap.BilinForm.toMatrix'
    (β.comp e.symm.toLinearMap e.symm.toLinearMap)

/-- The matrix represents the original pairing on ALL vectors,
not merely the images of basis elements. -/
theorem symplecticFormTransportMatrix_pairing
    {V I : Type*}
    [AddCommGroup V] [Module F2 V] [Fintype I]
    (β : LinearMap.BilinForm F2 V)
    (e : V ≃ₗ[F2] (I → F2))
    (u v : I → F2) :
    (Matrix.toBilin' (symplecticFormTransportMatrix β e)) u v =
      β (e.symm u) (e.symm v) := by
  unfold symplecticFormTransportMatrix
  rw [Matrix.toBilin'_toMatrix']
  rfl

/-- Alternation of the original form supplies both matrix
conditions needed by the zero-cross block construction. -/
theorem symplecticFormTransportMatrix_alternating
    {V I : Type*}
    [AddCommGroup V] [Module F2 V] [Fintype I]
    (β : LinearMap.BilinForm F2 V)
    (e : V ≃ₗ[F2] (I → F2))
    (hβ : β.IsAlt) :
    (∀ i, symplecticFormTransportMatrix β e i i = 0) ∧
    (∀ i j, symplecticFormTransportMatrix β e i j =
      symplecticFormTransportMatrix β e j i) := by
  have hcoord :
      (β.comp e.symm.toLinearMap e.symm.toLinearMap).IsAlt := by
    intro x
    exact hβ (e.symm x)
  exact symplecticAlternating_toMatrix_certificate _ hcoord

/-- Two isometric embeddings of the SAME source, whose coordinates
are adapted to that source, have identical common A-by-A matrix
blocks.  No nondegeneracy or perpendicular decomposition is used. -/
theorem symplecticFormTransportMatrix_commonBlock
    {VA VB VC A X Y : Type*}
    [AddCommGroup VA] [Module F2 VA]
    [AddCommGroup VB] [Module F2 VB]
    [AddCommGroup VC] [Module F2 VC]
    [Fintype A] [Fintype X] [Fintype Y]
    (βA : LinearMap.BilinForm F2 VA)
    (βB : LinearMap.BilinForm F2 VB)
    (βC : LinearMap.BilinForm F2 VC)
    (iB : VA →ₗ[F2] VB) (iC : VA →ₗ[F2] VC)
    (eA : VA ≃ₗ[F2] (A → F2))
    (eB : VB ≃ₗ[F2] (Sum A X → F2))
    (eC : VC ≃ₗ[F2] (Sum A Y → F2))
    (hBbase : ∀ a, eB (iB a) =
      symplecticBlockVectorCommonLeft (eA a))
    (hCbase : ∀ a, eC (iC a) =
      symplecticBlockVectorCommonRight (eA a))
    (hBiso : ∀ a a', βB (iB a) (iB a') = βA a a')
    (hCiso : ∀ a a', βC (iC a) (iC a') = βA a a') :
    ∀ a a' : A,
      symplecticFormTransportMatrix βB eB (.inl a) (.inl a') =
      symplecticFormTransportMatrix βC eC (.inl a) (.inl a') := by
  classical
  have hBcoord : ∀ a : A,
      eB.symm (Pi.single (Sum.inl a) (1 : F2)) =
      iB (eA.symm (Pi.single a (1 : F2))) := by
    intro a
    apply eB.injective
    calc
      eB (eB.symm (Pi.single (Sum.inl a) (1 : F2))) =
        Pi.single (Sum.inl a) (1 : F2) := eB.apply_symm_apply _
      _ = symplecticBlockVectorCommonLeft
          (eA (eA.symm (Pi.single a (1 : F2)))) := by
            rw [eA.apply_symm_apply, symplecticCommonLeft_single]
      _ = eB (iB (eA.symm (Pi.single a (1 : F2)))) :=
        (hBbase _).symm
  have hCcoord : ∀ a : A,
      eC.symm (Pi.single (Sum.inl a) (1 : F2)) =
      iC (eA.symm (Pi.single a (1 : F2))) := by
    intro a
    apply eC.injective
    calc
      eC (eC.symm (Pi.single (Sum.inl a) (1 : F2))) =
        Pi.single (Sum.inl a) (1 : F2) := eC.apply_symm_apply _
      _ = symplecticBlockVectorCommonRight
          (eA (eA.symm (Pi.single a (1 : F2)))) := by
            rw [eA.apply_symm_apply, symplecticCommonRight_single]
      _ = eC (iC (eA.symm (Pi.single a (1 : F2)))) :=
        (hCbase _).symm
  intro a a'
  simp only [symplecticFormTransportMatrix,
    LinearMap.BilinForm.toMatrix'_apply]
  change βB (eB.symm (Pi.single (.inl a) 1))
      (eB.symm (Pi.single (.inl a') 1)) =
    βC (eC.symm (Pi.single (.inl a) 1))
      (eC.symm (Pi.single (.inl a') 1))
  rw [hBcoord, hBcoord, hCcoord, hCcoord]
  exact (hBiso _ _).trans (hCiso _ _).symm

end SuccessorTree.NonPrecompact
