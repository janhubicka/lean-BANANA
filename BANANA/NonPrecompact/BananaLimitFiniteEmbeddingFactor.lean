import BANANA.NonPrecompact.BananaLimitFiniteAge
import BANANA.NonPrecompact.PerfectHomogeneity

/-!
# Factor finite BANANA embeddings into the limit through a perfect block

Two embeddings of the same finite BANANA structure into the explicit
finitely supported rational-coordinate pairing have all their vectors
inside a common finite perfect coordinate block. Restriction and the
block's standard coordinate equivalence convert each to an embedding
into the corresponding standard perfect pairing.

This is the finite-support reduction for global ultrahomogeneity.
No global automorphism is constructed in this module.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

namespace BananaMatrixEmbeddingToLimit

/-- Restrict an embedding with both image sorts supported on S to
a standard perfect pairing with S.card coordinates. -/
noncomputable def factorToPerfectBlock
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (e : BananaMatrixEmbeddingToLimit A) (S : Finset ℚ)
    (hL : ∀ x, e.left x ∈ bananaLimitBlock S)
    (hR : ∀ y, e.right y ∈ bananaLimitBlock S) :
    BananaMatrixEmbedding A (perfectBanana S.card) := by
  classical
  let E := bananaLimitBlockStandardEquiv S
  let fL : (Fin l → F2) →ₗ[F2] bananaLimitBlock S :=
    e.left.codRestrict (bananaLimitBlock S) hL
  let fR : (Fin r → F2) →ₗ[F2] bananaLimitBlock S :=
    e.right.codRestrict (bananaLimitBlock S) hR
  refine {
    left := E.symm.toLinearMap.comp fL
    right := E.symm.toLinearMap.comp fR
    left_injective := ?_
    right_injective := ?_
    pairing_apply := ?_
  }
  · intro x y h
    change E.symm (fL x) = E.symm (fL y) at h
    apply e.left_injective
    exact congrArg Subtype.val (E.symm.injective h)
  · intro x y h
    change E.symm (fR x) = E.symm (fR y) at h
    apply e.right_injective
    exact congrArg Subtype.val (E.symm.injective h)
  · intro x y
    simp only [perfectBanana_eval, LinearMap.comp_apply]
    change (E.symm (fL x)) ⬝ᵥ (E.symm (fR y)) =
      A.eval x y
    calc
      (E.symm (fL x)) ⬝ᵥ (E.symm (fR y)) =
        bananaLimitPairing (fL x : BananaLimitVector)
          (fR y : BananaLimitVector) := by
          simpa [E] using
            (bananaLimitBlockStandardEquiv_pairing S
              (E.symm (fL x)) (E.symm (fR y))).symm
      _ = A.eval x y := e.pairing_apply x y

/-- Factoring and re-embedding gives the same left-sort map. -/
theorem factorToPerfectBlock_left
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (e : BananaMatrixEmbeddingToLimit A) (S : Finset ℚ)
    (hL : ∀ x, e.left x ∈ bananaLimitBlock S)
    (hR : ∀ y, e.right y ∈ bananaLimitBlock S)
    (x : Fin l → F2) :
    (bananaLimitBlockStandardEmbedding S).left
      ((e.factorToPerfectBlock S hL hR).left x) = e.left x := by
  classical
  let E := bananaLimitBlockStandardEquiv S
  let fL : (Fin l → F2) →ₗ[F2] bananaLimitBlock S :=
    e.left.codRestrict (bananaLimitBlock S) hL
  change (E (E.symm (fL x)) : BananaLimitVector) = e.left x
  rw [E.apply_symm_apply]
  rfl

/-- Factoring and re-embedding gives the same right-sort map. -/
theorem factorToPerfectBlock_right
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (e : BananaMatrixEmbeddingToLimit A) (S : Finset ℚ)
    (hL : ∀ x, e.left x ∈ bananaLimitBlock S)
    (hR : ∀ y, e.right y ∈ bananaLimitBlock S)
    (y : Fin r → F2) :
    (bananaLimitBlockStandardEmbedding S).right
      ((e.factorToPerfectBlock S hL hR).right y) = e.right y := by
  classical
  let E := bananaLimitBlockStandardEquiv S
  let fR : (Fin r → F2) →ₗ[F2] bananaLimitBlock S :=
    e.right.codRestrict (bananaLimitBlock S) hR
  change (E (E.symm (fR y)) : BananaLimitVector) = e.right y
  rw [E.apply_symm_apply]
  rfl

/-- Two finite embeddings into the explicit limit fit in one finite
perfect block, simultaneously on both sorts and for both copies. -/
theorem exists_common_finite_block
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (e₁ e₂ : BananaMatrixEmbeddingToLimit A) :
    ∃ S : Finset ℚ,
      (∀ x, e₁.left x ∈ bananaLimitBlock S) ∧
      (∀ y, e₁.right y ∈ bananaLimitBlock S) ∧
      (∀ x, e₂.left x ∈ bananaLimitBlock S) ∧
      (∀ y, e₂.right y ∈ bananaLimitBlock S) := by
  classical
  let left : Finset BananaLimitVector :=
    ((Finset.univ : Finset (Fin l → F2)).image e₁.left) ∪
    ((Finset.univ : Finset (Fin l → F2)).image e₂.left)
  let right : Finset BananaLimitVector :=
    ((Finset.univ : Finset (Fin r → F2)).image e₁.right) ∪
    ((Finset.univ : Finset (Fin r → F2)).image e₂.right)
  refine ⟨bananaLimitCommonSupport left right, ?_, ?_, ?_, ?_⟩
  · intro x
    apply bananaLimit_left_mem_common_block left right
    exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
  · intro y
    apply bananaLimit_right_mem_common_block left right
    exact Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩)
  · intro x
    apply bananaLimit_left_mem_common_block left right
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
  · intro y
    apply bananaLimit_right_mem_common_block left right
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩)

end BananaMatrixEmbeddingToLimit

end SuccessorTree.NonPrecompact
