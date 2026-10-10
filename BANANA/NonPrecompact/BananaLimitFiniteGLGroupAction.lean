import BANANA.NonPrecompact.BananaLimitBlockLiftGroupLaw
import BANANA.NonPrecompact.BananaLimitFiniteGLAction
import BANANA.NonPrecompact.CompletionAutomorphismHom

/-!
# Group laws of finite GL actions on the countable BANANA limit

For every finite rational-coordinate block S, the map from
GL(|S|, F₂) to the pair of global linear automorphisms obtained
by acting contragrediently and fixing the outside coordinates
respects the identity and composition on *both* sorts.

Combined with the already verified finite parameter type, these
calculations show that each fixed finite block yields a finite
subgroup of the pairing-preserving automorphism group.
-/

namespace SuccessorTree.NonPrecompact

/-- Conjugation to a finite block respects the identity on the left. -/
theorem bananaLimitFiniteGLBlockLeft_refl (S : Finset ℚ) :
    bananaLimitFiniteGLBlockLeft S
      (LinearEquiv.refl F2 (Fin S.card → F2)) =
      LinearEquiv.refl F2 (bananaLimitBlock S) := by
  apply LinearEquiv.ext
  intro u
  simp [bananaLimitFiniteGLBlockLeft, LinearEquiv.trans_apply]

/-- Conjugation to a finite block respects the identity on the right. -/
theorem bananaLimitFiniteGLBlockRight_refl (S : Finset ℚ) :
    bananaLimitFiniteGLBlockRight S
      (LinearEquiv.refl F2 (Fin S.card → F2)) =
      LinearEquiv.refl F2 (bananaLimitBlock S) := by
  apply LinearEquiv.ext
  intro u
  simp [bananaLimitFiniteGLBlockRight,
    BananaMatrixStructure.dotContragredient_refl,
    LinearEquiv.trans_apply]

/-- The left finite block action respects composition. -/
theorem bananaLimitFiniteGLBlockLeft_trans
    (S : Finset ℚ) (f g : FinitePerfectGL S.card) :
    bananaLimitFiniteGLBlockLeft S (f.trans g) =
      (bananaLimitFiniteGLBlockLeft S f).trans
        (bananaLimitFiniteGLBlockLeft S g) := by
  apply LinearEquiv.ext
  intro u
  simp [bananaLimitFiniteGLBlockLeft, LinearEquiv.trans_apply]

/-- The right contragredient finite block action also respects
composition in the same order. -/
theorem bananaLimitFiniteGLBlockRight_trans
    (S : Finset ℚ) (f g : FinitePerfectGL S.card) :
    bananaLimitFiniteGLBlockRight S (f.trans g) =
      (bananaLimitFiniteGLBlockRight S f).trans
        (bananaLimitFiniteGLBlockRight S g) := by
  apply LinearEquiv.ext
  intro u
  simp [bananaLimitFiniteGLBlockRight,
    BananaMatrixStructure.dotContragredient_trans,
    LinearEquiv.trans_apply]

/-- Both globally lifted actions send the identity finite matrix
automorphism to the corresponding global identity. -/
theorem bananaLimitFiniteGLAction_refl (S : Finset ℚ) :
    (bananaLimitFiniteGLAction S
      (LinearEquiv.refl F2 (Fin S.card → F2))).1 =
      LinearEquiv.refl F2 BananaLimitVector ∧
    (bananaLimitFiniteGLAction S
      (LinearEquiv.refl F2 (Fin S.card → F2))).2 =
      LinearEquiv.refl F2 BananaLimitVector := by
  constructor
  · change bananaLimitBlockLift S
      (bananaLimitFiniteGLBlockLeft S
        (LinearEquiv.refl F2 (Fin S.card → F2))) =
      LinearEquiv.refl F2 BananaLimitVector
    rw [bananaLimitFiniteGLBlockLeft_refl, bananaLimitBlockLift_refl]
  · change bananaLimitBlockLift S
      (bananaLimitFiniteGLBlockRight S
        (LinearEquiv.refl F2 (Fin S.card → F2))) =
      LinearEquiv.refl F2 BananaLimitVector
    rw [bananaLimitFiniteGLBlockRight_refl, bananaLimitBlockLift_refl]

/-- Composition of two global actions from one finite GL stage
agrees with the global action of the product, on both sorts. -/
theorem bananaLimitFiniteGLAction_trans
    (S : Finset ℚ) (f g : FinitePerfectGL S.card) :
    (bananaLimitFiniteGLAction S (f.trans g)).1 =
      (bananaLimitFiniteGLAction S f).1.trans
        (bananaLimitFiniteGLAction S g).1 ∧
    (bananaLimitFiniteGLAction S (f.trans g)).2 =
      (bananaLimitFiniteGLAction S f).2.trans
        (bananaLimitFiniteGLAction S g).2 := by
  constructor
  · change bananaLimitBlockLift S
      (bananaLimitFiniteGLBlockLeft S (f.trans g)) =
      (bananaLimitBlockLift S (bananaLimitFiniteGLBlockLeft S f)).trans
        (bananaLimitBlockLift S (bananaLimitFiniteGLBlockLeft S g))
    rw [bananaLimitFiniteGLBlockLeft_trans, bananaLimitBlockLift_trans]
  · change bananaLimitBlockLift S
      (bananaLimitFiniteGLBlockRight S (f.trans g)) =
      (bananaLimitBlockLift S (bananaLimitFiniteGLBlockRight S f)).trans
        (bananaLimitBlockLift S (bananaLimitFiniteGLBlockRight S g))
    rw [bananaLimitFiniteGLBlockRight_trans, bananaLimitBlockLift_trans]

end SuccessorTree.NonPrecompact
