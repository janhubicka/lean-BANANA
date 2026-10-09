import BANANA.NonPrecompact.BananaArbitraryAmalgamTools
import BANANA.NonPrecompact.BananaDirectSum
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Hereditary closure and joint embedding for finite BANANA pairings

A substructure of a finite BANANA pairing is given by a pair of
vector subspaces with the restricted pairing. Choose linear bases of
these two subspaces. Their coordinate spaces define a finite matrix
pairing, which embeds in the original structure with *exactly* the
prescribed subspace images. No nondegeneracy is assumed.

Joint embedding is the block-diagonal direct sum of two finite
pairings. These are finite structural components of the Fraïssé
class argument, separate from the eventual explicit countable limit.
-/

namespace SuccessorTree.NonPrecompact

open Module

/-- Every pair of subspaces of a finite BANANA structure is realised
as the two sorts of an embedded finite matrix structure. The
pairing is the restriction of the original pairing, represented
after choosing bases. -/
theorem BananaMatrixStructure.exists_substructure_with_ranges
    {l r : ℕ}
    (A : BananaMatrixStructure l r)
    (U : Submodule F2 (Fin l → F2))
    (V : Submodule F2 (Fin r → F2)) :
    ∃ l' r' : ℕ,
    ∃ B : BananaMatrixStructure l' r',
    ∃ e : BananaMatrixEmbedding B A,
      LinearMap.range e.left = U ∧
      LinearMap.range e.right = V := by
  classical
  let l' : ℕ := finrank F2 U
  let r' : ℕ := finrank F2 V
  have hdL : finrank F2 (Fin l' → F2) = finrank F2 U := by
    simp [l', Module.finrank_fintype_fun_eq_card]
  have hdR : finrank F2 (Fin r' → F2) = finrank F2 V := by
    simp [r', Module.finrank_fintype_fun_eq_card]
  let eL : (Fin l' → F2) ≃ₗ[F2] U :=
    LinearEquiv.ofFinrankEq (Fin l' → F2) U hdL
  let eR : (Fin r' → F2) ≃ₗ[F2] V :=
    LinearEquiv.ofFinrankEq (Fin r' → F2) V hdR
  let fL : (Fin l' → F2) →ₗ[F2] (Fin l → F2) :=
    U.subtype.comp eL.toLinearMap
  let fR : (Fin r' → F2) →ₗ[F2] (Fin r → F2) :=
    V.subtype.comp eR.toLinearMap
  let B : BananaMatrixStructure l' r' :=
    bananaPairingPullback A fL fR
  let f : BananaMatrixEmbedding B A :=
    { left := fL
      right := fR
      left_injective := U.injective_subtype.comp eL.injective
      right_injective := V.injective_subtype.comp eR.injective
      pairing_apply := by
        intro x y
        exact (bananaPairingPullback_eval A fL fR x y).symm }
  refine ⟨l', r', B, f, ?_, ?_⟩
  · change LinearMap.range fL = U
    apply Submodule.ext
    intro z
    constructor
    · rintro ⟨x, rfl⟩
      exact (eL x).property
    · intro hz
      obtain ⟨x, hx⟩ := eL.surjective ⟨z, hz⟩
      refine ⟨x, ?_⟩
      exact congrArg Subtype.val hx
  · change LinearMap.range fR = V
    apply Submodule.ext
    intro z
    constructor
    · rintro ⟨x, rfl⟩
      exact (eR x).property
    · intro hz
      obtain ⟨x, hx⟩ := eR.surjective ⟨z, hz⟩
      refine ⟨x, ?_⟩
      exact congrArg Subtype.val hx

/-- Two finite BANANA structures embed into a common finite
structure, given explicitly by their zero-cross-pairing direct sum. -/
theorem BananaMatrixStructure.exists_joint_embedding
    {lB rB lC rC : ℕ}
    (B : BananaMatrixStructure lB rB)
    (C : BananaMatrixStructure lC rC) :
    ∃ D : BananaMatrixStructure (lB + lC) (rB + rC),
      Nonempty (BananaMatrixEmbedding B D) ∧
      Nonempty (BananaMatrixEmbedding C D) := by
  refine ⟨bananaDirectSum B C, ?_, ?_⟩
  · exact ⟨B.directSumInlEmbedding C⟩
  · exact ⟨B.directSumInrEmbedding C⟩

end SuccessorTree.NonPrecompact
