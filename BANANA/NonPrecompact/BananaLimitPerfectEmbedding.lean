import BANANA.NonPrecompact.BananaPerfectFiniteBlocks
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Standard perfect finite pairings inside the explicit BANANA limit

A finite rational-coordinate block with n coordinates is a standard
perfect pairing of dimension n, after reindexing the coordinates.
This will be combined with the already kernel-checked completion
embedding to establish universality of the explicit countable model.

The proof is in the finite-support vector-space representation:
no assertion of full Fraïssé homogeneity is made in this module.
-/

namespace SuccessorTree.NonPrecompact

/-- Every finite dimension is realised by a finite set of rational
coordinate indices. -/
theorem exists_rational_coordinates (n : ℕ) :
    ∃ S : Finset ℚ, S.card = n := by
  classical
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq ℚ n
  exact ⟨S, hS⟩

/-- A finite rational-coordinate block of any prescribed dimension
is linearly equivalent to the usual binary coordinate space, with
exactly the standard perfect pairing. -/
theorem exists_perfect_block_in_banana_limit (n : ℕ) :
    ∃ S : Finset ℚ,
    ∃ E : (Fin n → F2) ≃ₗ[F2] (bananaLimitBlock S),
      ∀ x y : Fin n → F2,
        bananaLimitPairing (E x) (E y) = x ⬝ᵥ y := by
  classical
  obtain ⟨S, hcard⟩ := exists_rational_coordinates n
  let e : (S : Type) ≃ Fin n :=
    Fintype.equivFinOfCardEq (by simpa using hcard)
  let E : (Fin n → F2) ≃ₗ[F2] bananaLimitBlock S :=
    (LinearEquiv.funCongrLeft F2 F2 e).trans
      (bananaLimitBlockEquiv S).symm
  refine ⟨S, E, ?_⟩
  intro x y
  rw [bananaLimitBlock_pairing_eq_dotProduct]
  simp only [E, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  change (fun q : S => x (e q)) ⬝ᵥ
      (fun q : S => y (e q)) = x ⬝ᵥ y
  simp only [dotProduct]
  simpa only [Equiv.apply_symm_apply] using
    (Equiv.sum_comp e.symm
      (fun q : S => x (e q) * y (e q))).symm

end SuccessorTree.NonPrecompact
