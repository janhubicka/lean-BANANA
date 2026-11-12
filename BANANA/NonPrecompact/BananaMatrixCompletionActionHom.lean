import BANANA.NonPrecompact.BananaMatrixAutGroup
import BANANA.NonPrecompact.CompletionAutomorphismHom

/-!
# Canonical completion action as a homomorphism of actual finite BANANA groups

The finite pairing-preserving automorphism group of A acts on its
perfect completion via the left action f ⊕ (g⁻¹)* and the associated
right contragredient.  In the source and target groups, multiplication
means functional composition, consistent with LinearEquiv.mul_apply.

The induced automorphism extends f and g on the two original sorts,
and its identity/composition laws are stated as one MonoidHom.
The finite representative-choice/groupoid coherence is still separate.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- The completion of a finite pairing admits a canonical group action
of its own two-sorted pairing-preserving automorphism group. -/
noncomputable def bananaMatrixCompletionActionHom
    {l r : ℕ} (A : BananaMatrixStructure l r) :
    BananaMatrixAutGroup A →*
      BananaMatrixAutGroup (perfectBanana (l + r)) where
  toFun f := by
    refine ⟨⟨BananaMatrixStructure.completionLeftEquiv f.1.1 f.1.2,
      dotContragredient
        (BananaMatrixStructure.completionLeftEquiv f.1.1 f.1.2)⟩, ?_⟩
    intro x y
    exact (BananaMatrixStructure.completionAutomorphism
      f.1.1 f.1.2).pairing_apply x y
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · exact BananaMatrixStructure.completionLeftEquiv_refl
    · change dotContragredient
        (BananaMatrixStructure.completionLeftEquiv
          (LinearEquiv.refl F2 (Fin l → F2))
          (LinearEquiv.refl F2 (Fin r → F2))) =
        LinearEquiv.refl F2 (Fin (l + r) → F2)
      rw [BananaMatrixStructure.completionLeftEquiv_refl]
      exact BananaMatrixStructure.dotContragredient_refl
  map_mul' := by
    intro f g
    have hleft :
        BananaMatrixStructure.completionLeftEquiv
          (f.1.1 * g.1.1) (f.1.2 * g.1.2) =
        BananaMatrixStructure.completionLeftEquiv f.1.1 f.1.2 *
          BananaMatrixStructure.completionLeftEquiv g.1.1 g.1.2 := by
      change BananaMatrixStructure.completionLeftEquiv
          (g.1.1.trans f.1.1) (g.1.2.trans f.1.2) =
        (BananaMatrixStructure.completionLeftEquiv g.1.1 g.1.2).trans
          (BananaMatrixStructure.completionLeftEquiv f.1.1 f.1.2)
      exact BananaMatrixStructure.completionLeftEquiv_trans
        g.1.1 f.1.1 g.1.2 f.1.2
    apply Subtype.ext
    apply Prod.ext
    · exact hleft
    · change dotContragredient
        (BananaMatrixStructure.completionLeftEquiv
          (f.1.1 * g.1.1) (f.1.2 * g.1.2)) =
          dotContragredient
            (BananaMatrixStructure.completionLeftEquiv f.1.1 f.1.2) *
          dotContragredient
            (BananaMatrixStructure.completionLeftEquiv g.1.1 g.1.2)
      rw [hleft]
      change dotContragredient
          ((BananaMatrixStructure.completionLeftEquiv g.1.1 g.1.2).trans
            (BananaMatrixStructure.completionLeftEquiv f.1.1 f.1.2)) =
        (dotContragredient
          (BananaMatrixStructure.completionLeftEquiv g.1.1 g.1.2)).trans
          (dotContragredient
            (BananaMatrixStructure.completionLeftEquiv f.1.1 f.1.2))
      exact BananaMatrixStructure.dotContragredient_trans
        (BananaMatrixStructure.completionLeftEquiv g.1.1 g.1.2)
        (BananaMatrixStructure.completionLeftEquiv f.1.1 f.1.2)

/-- The group homomorphism extends its source automorphism on the left. -/
theorem bananaMatrixCompletionActionHom_extends_left
    {l r : ℕ} (A : BananaMatrixStructure l r)
    (f : BananaMatrixAutGroup A) (x : Fin l → F2) :
    (bananaMatrixCompletionActionHom A f).1.1 (A.completionLeft x) =
      A.completionLeft (f.1.1 x) :=
  BananaMatrixStructure.completionAutomorphism_left_completion
    A f.1.1 f.1.2 x

/-- The group homomorphism extends its source automorphism on the right,
using explicitly the pairing-preservation hypothesis. -/
theorem bananaMatrixCompletionActionHom_extends_right
    {l r : ℕ} (A : BananaMatrixStructure l r)
    (f : BananaMatrixAutGroup A) (y : Fin r → F2) :
    (bananaMatrixCompletionActionHom A f).1.2 (A.completionRight y) =
      A.completionRight (f.1.2 y) :=
  BananaMatrixStructure.completionAutomorphism_right_completion
    A f.1.1 f.1.2 f.pairing_apply y

end SuccessorTree.NonPrecompact
