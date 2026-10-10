import BANANA.NonPrecompact.FinitePerfectGL
import BANANA.NonPrecompact.BananaLimitBlockPairLift
import BANANA.NonPrecompact.BananaLimitBlockCofinality

/-!
# Finite perfect-block general linear actions on the BANANA limit

The standard perfect pairing on a rational-coordinate block admits
the finite automorphism group GL(|S|, F₂), acting on the left through
the given linear equivalence and on the right through its
contragredient. Conjugating through the standard-coordinate
equivalence and extending by the identity on coordinates outside S
produces global automorphisms of the explicit countable pairing.

This is the finite subgroup action used in the circulation proof of
amenability. Its density in the full automorphism group is separate.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- Action of a finite linear equivalence on the left block. -/
noncomputable def bananaLimitFiniteGLBlockLeft
    (S : Finset ℚ) (h : FinitePerfectGL S.card) :
    bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S :=
  ((bananaLimitBlockStandardEquiv S).symm.trans h).trans
    (bananaLimitBlockStandardEquiv S)

/-- The matching contragredient action on the right block. -/
noncomputable def bananaLimitFiniteGLBlockRight
    (S : Finset ℚ) (h : FinitePerfectGL S.card) :
    bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S :=
  ((bananaLimitBlockStandardEquiv S).symm.trans
    (dotContragredient h)).trans
    (bananaLimitBlockStandardEquiv S)

/-- The two finite-block maps preserve every cross-pairing within S. -/
theorem bananaLimitFiniteGLBlock_pairing
    (S : Finset ℚ) (h : FinitePerfectGL S.card)
    (u v : bananaLimitBlock S) :
    bananaLimitPairing
      (bananaLimitFiniteGLBlockLeft S h u : BananaLimitVector)
      (bananaLimitFiniteGLBlockRight S h v : BananaLimitVector) =
    bananaLimitPairing (u : BananaLimitVector)
      (v : BananaLimitVector) := by
  classical
  let E := bananaLimitBlockStandardEquiv S
  change bananaLimitPairing
    (E (h (E.symm u)) : BananaLimitVector)
    (E (dotContragredient h (E.symm v)) : BananaLimitVector) =
    bananaLimitPairing (u : BananaLimitVector) (v : BananaLimitVector)
  calc
    bananaLimitPairing
        (E (h (E.symm u)) : BananaLimitVector)
        (E (dotContragredient h (E.symm v)) : BananaLimitVector) =
      h (E.symm u) ⬝ᵥ dotContragredient h (E.symm v) :=
        bananaLimitBlockStandardEquiv_pairing S _ _
    _ = (E.symm u) ⬝ᵥ (E.symm v) :=
      dotContragredient_pairing h _ _
    _ = bananaLimitPairing (u : BananaLimitVector)
        (v : BananaLimitVector) := by
      have he :=
        (bananaLimitBlockStandardEquiv_pairing S
          (E.symm u) (E.symm v)).symm
      change (E.symm u) ⬝ᵥ (E.symm v) =
        bananaLimitPairing
          (E (E.symm u) : BananaLimitVector)
          (E (E.symm v) : BananaLimitVector) at he
      simpa only [LinearEquiv.apply_symm_apply] using he

/-- A finite perfect-pair GL transformation extended by the identity
to the full countable pairing on both sorts. -/
noncomputable def bananaLimitFiniteGLAction
    (S : Finset ℚ) (h : FinitePerfectGL S.card) :
    (BananaLimitVector ≃ₗ[F2] BananaLimitVector) ×
      (BananaLimitVector ≃ₗ[F2] BananaLimitVector) :=
  (bananaLimitBlockLift S (bananaLimitFiniteGLBlockLeft S h),
   bananaLimitBlockLift S (bananaLimitFiniteGLBlockRight S h))

/-- Every finite-block GL action is a global pairing automorphism. -/
theorem bananaLimitFiniteGLAction_pairing
    (S : Finset ℚ) (h : FinitePerfectGL S.card)
    (x y : BananaLimitVector) :
    bananaLimitPairing
      ((bananaLimitFiniteGLAction S h).1 x)
      ((bananaLimitFiniteGLAction S h).2 y) =
      bananaLimitPairing x y := by
  exact bananaLimitBlockLift_pairing S
    (bananaLimitFiniteGLBlockLeft S h)
    (bananaLimitFiniteGLBlockRight S h)
    (bananaLimitFiniteGLBlock_pairing S h) x y

/-- On the left, the global action agrees with h on the finite
standard-coordinate block. -/
theorem bananaLimitFiniteGLAction_left_on_block
    (S : Finset ℚ) (h : FinitePerfectGL S.card)
    (x : Fin S.card → F2) :
    (bananaLimitFiniteGLAction S h).1
      ((bananaLimitBlockStandardEquiv S x : bananaLimitBlock S) :
        BananaLimitVector) =
      (bananaLimitBlockStandardEquiv S (h x) : BananaLimitVector) := by
  rw [bananaLimitFiniteGLAction]
  change bananaLimitBlockLift S (bananaLimitFiniteGLBlockLeft S h)
      (bananaLimitBlockStandardEquiv S x : BananaLimitVector) = _
  rw [bananaLimitBlockLift_on_block]
  simp only [bananaLimitFiniteGLBlockLeft, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

/-- On the right, the global action agrees with the contragredient
on the finite standard-coordinate block. -/
theorem bananaLimitFiniteGLAction_right_on_block
    (S : Finset ℚ) (h : FinitePerfectGL S.card)
    (y : Fin S.card → F2) :
    (bananaLimitFiniteGLAction S h).2
      ((bananaLimitBlockStandardEquiv S y : bananaLimitBlock S) :
        BananaLimitVector) =
      (bananaLimitBlockStandardEquiv S (dotContragredient h y) :
        BananaLimitVector) := by
  rw [bananaLimitFiniteGLAction]
  change bananaLimitBlockLift S (bananaLimitFiniteGLBlockRight S h)
      (bananaLimitBlockStandardEquiv S y : BananaLimitVector) = _
  rw [bananaLimitBlockLift_on_block]
  simp only [bananaLimitFiniteGLBlockRight, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]

end SuccessorTree.NonPrecompact
