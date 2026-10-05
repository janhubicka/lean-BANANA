import BANANA.NonPrecompact.PerfectBlockConjugator

/-!
# Prescribing the left range of an embedded perfect BANANA block

The degree-one half of the BANANA Ramsey-degree classification needs the
following finite linear-algebra interface.  Given a D-dimensional subspace
of an ambient standard perfect pairing, one can realise it as the left side
of an embedded copy of the D-dimensional perfect pairing.

This is the formal version of the manuscript step which chooses a basis of
the monochromatic space and extends its dual coordinate functionals to the
ambient vector space.
-/

namespace SuccessorTree.NonPrecompact

open LinearMap Module

namespace BananaMatrixStructure

/-- The standard first D-dimensional left block in the ambient coordinate
space of dimension D+k. -/
def standardPerfectLeftRange (D k : ℕ) :
    Submodule F2 (Fin (D + k) → F2) :=
  LinearMap.range (standardPerfectBlockEmbedding D k).left

theorem finrank_standardPerfectLeftRange (D k : ℕ) :
    finrank F2 (standardPerfectLeftRange D k) = D := by
  unfold standardPerfectLeftRange
  rw [LinearMap.finrank_range_of_inj
    (standardPerfectBlockEmbedding D k).left_injective]
  simp [Module.finrank_fintype_fun_eq_card]

/-- Any D-dimensional left subspace of the ambient perfect pairing is the
left range of an embedded standard perfect D-block. -/
theorem exists_perfectBlockEmbedding_leftRange_eq
    {D k : ℕ}
    (W : Submodule F2 (Fin (D + k) → F2))
    (hW : finrank F2 W = D) :
    ∃ E :
        BananaMatrixEmbedding
          (perfectBanana D)
          (perfectBanana (D + k)),
      LinearMap.range E.left = W := by
  let U : Submodule F2 (Fin (D + k) → F2) :=
    standardPerfectLeftRange D k
  have hU : finrank F2 U = D := by
    simpa [U] using finrank_standardPerfectLeftRange D k
  let e : U ≃ₗ[F2] W :=
    LinearEquiv.ofFinrankEq U W (hU.trans hW.symm)
  obtain ⟨h, hext⟩ :=
    exists_linearEquiv_extends_submoduleEquiv e
      (V := Fin (D + k) → F2)
      (V' := Fin (D + k) → F2)
      rfl
  let H :
      BananaMatrixEmbedding
        (perfectBanana (D + k))
        (perfectBanana (D + k)) :=
    perfectPairAutomorphismOfLinearEquiv h
  let E :
      BananaMatrixEmbedding
        (perfectBanana D)
        (perfectBanana (D + k)) :=
    BananaMatrixEmbedding.comp H (standardPerfectBlockEmbedding D k)
  refine ⟨E, ?_⟩
  apply le_antisymm
  · rintro z ⟨x, rfl⟩
    let u : U :=
      ⟨(standardPerfectBlockEmbedding D k).left x, by
        exact ⟨x, rfl⟩⟩
    have hu := hext u
    change h (u : Fin (D + k) → F2) = (e u : W) at hu
    change H.left ((standardPerfectBlockEmbedding D k).left x) ∈ W
    change h ((standardPerfectBlockEmbedding D k).left x) ∈ W
    rw [show (standardPerfectBlockEmbedding D k).left x = (u : Fin (D + k) → F2) by rfl,
      hu]
    exact (e u).property
  · intro z hz
    let w : W := ⟨z, hz⟩
    obtain ⟨u, hu⟩ := e.surjective w
    obtain ⟨x, hx⟩ := u.property
    refine ⟨x, ?_⟩
    have he := hext u
    change h (u : Fin (D + k) → F2) = (e u : W) at he
    change E.left x = z
    change h ((standardPerfectBlockEmbedding D k).left x) = z
    rw [hx]
    rw [he]
    have hval := congrArg Subtype.val hu
    exact hval

/-- Swap the two sorts of an embedding between standard perfect pairings.
The standard dot product is symmetric, so this again preserves the pairing. -/
def swapPerfectBlockEmbedding
    {D n : ℕ}
    (E :
      BananaMatrixEmbedding
        (perfectBanana D)
        (perfectBanana n)) :
    BananaMatrixEmbedding
      (perfectBanana D)
      (perfectBanana n) where
  left := E.right
  right := E.left
  left_injective := E.right_injective
  right_injective := E.left_injective
  pairing_apply := by
    intro x y
    simpa only [perfectBanana_eval, dotProduct_comm] using
      E.pairing_apply y x

/-- The right-sort analogue of
`exists_perfectBlockEmbedding_leftRange_eq`. -/
theorem exists_perfectBlockEmbedding_rightRange_eq
    {D k : ℕ}
    (W : Submodule F2 (Fin (D + k) → F2))
    (hW : finrank F2 W = D) :
    ∃ E :
        BananaMatrixEmbedding
          (perfectBanana D)
          (perfectBanana (D + k)),
      LinearMap.range E.right = W := by
  obtain ⟨E, hE⟩ :=
    exists_perfectBlockEmbedding_leftRange_eq W hW
  refine ⟨swapPerfectBlockEmbedding E, ?_⟩
  exact hE

end BananaMatrixStructure

end SuccessorTree.NonPrecompact
