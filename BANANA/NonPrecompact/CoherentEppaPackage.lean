import BANANA.NonPrecompact.AlignedCompletionEmbedding
import BANANA.NonPrecompact.EmbeddedCompletionAction
import BANANA.NonPrecompact.CompletionAutomorphism

/-!
# Packaged coherent ambient action for BANANA completions

This file packages the finite algebra used in the coherent-EPPA proof.

Starting from an arbitrary embedding of the perfect completion of a finite
BANANA structure into a larger standard perfect pairing, we first align that
embedding with a prescribed copy of the original structure.  The coherent
completion action is then conjugated into the ambient perfect pairing.

The resulting ambient automorphisms extend the prescribed source
automorphisms and satisfy the identity and composition laws on both sorts.
The remaining manuscript-level bookkeeping for coherent EPPA is only the
finite choice of representatives of substructures and transport between
isomorphic representatives.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

namespace BananaMatrixStructure

/-- Finite-algebra package used in the BANANA coherent-EPPA proof.

The aligned embedding `E` contains the prescribed copy `j(A)`.  Every
pairing-preserving pair of linear equivalences `(f,g)` of `A` induces an
ambient perfect-pair automorphism extending `f` and `g` on that copy.
Moreover the ambient construction sends identities to identities and
preserves composition on both sorts. -/
theorem exists_alignedCoherentAmbientAction
    {l r k : ℕ}
    (A : BananaMatrixStructure l r)
    (j :
      BananaMatrixEmbedding
        A
        (perfectBanana ((l + r) + k)))
    (E₀ :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana ((l + r) + k))) :
    ∃ E :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana ((l + r) + k)),
      (∀ x, E.left (A.completionLeft x) = j.left x) ∧
      (∀ y, E.right (A.completionRight y) = j.right y) ∧
      (∀
          (f : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
          (g : (Fin r → F2) ≃ₗ[F2] (Fin r → F2)),
        (∀ x y, A.eval (f x) (g y) = A.eval x y) →
          (∀ x,
            (embeddedCompletionAmbientAutomorphism E f g).left
                (j.left x) =
              j.left (f x)) ∧
          (∀ y,
            (embeddedCompletionAmbientAutomorphism E f g).right
                (j.right y) =
              j.right (g y))) ∧
      (embeddedCompletionAmbientAutomorphism E
          (LinearEquiv.refl F2 (Fin l → F2))
          (LinearEquiv.refl F2 (Fin r → F2))).left =
        LinearMap.id ∧
      (embeddedCompletionAmbientAutomorphism E
          (LinearEquiv.refl F2 (Fin l → F2))
          (LinearEquiv.refl F2 (Fin r → F2))).right =
        LinearMap.id ∧
      (∀
          (f₁ f₂ : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
          (g₁ g₂ : (Fin r → F2) ≃ₗ[F2] (Fin r → F2)),
        (embeddedCompletionAmbientAutomorphism E
            (f₁.trans f₂) (g₁.trans g₂)).left =
          (BananaMatrixEmbedding.comp
            (embeddedCompletionAmbientAutomorphism E f₂ g₂)
            (embeddedCompletionAmbientAutomorphism E f₁ g₁)).left) ∧
      (∀
          (f₁ f₂ : (Fin l → F2) ≃ₗ[F2] (Fin l → F2))
          (g₁ g₂ : (Fin r → F2) ≃ₗ[F2] (Fin r → F2)),
        (embeddedCompletionAmbientAutomorphism E
            (f₁.trans f₂) (g₁.trans g₂)).right =
          (BananaMatrixEmbedding.comp
            (embeddedCompletionAmbientAutomorphism E f₂ g₂)
            (embeddedCompletionAmbientAutomorphism E f₁ g₁)).right) := by
  obtain ⟨E, hleft, hright⟩ :=
    A.exists_alignedCompletionEmbedding j E₀
  refine ⟨E, hleft, hright, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g hpair
    constructor
    · intro x
      calc
        (embeddedCompletionAmbientAutomorphism E f g).left
              (j.left x) =
            (embeddedCompletionAmbientAutomorphism E f g).left
              (E.left (A.completionLeft x)) := by
                rw [hleft x]
        _ = E.left
              (completionLeftEquiv f g (A.completionLeft x)) :=
            embeddedCompletionAmbientAutomorphism_left
              E f g (A.completionLeft x)
        _ = E.left (A.completionLeft (f x)) := by
            have h :=
              completionAutomorphism_left_completion A f g x
            change
              completionLeftEquiv f g (A.completionLeft x) =
                A.completionLeft (f x) at h
            exact congrArg E.left h
        _ = j.left (f x) := hleft (f x)
    · intro y
      calc
        (embeddedCompletionAmbientAutomorphism E f g).right
              (j.right y) =
            (embeddedCompletionAmbientAutomorphism E f g).right
              (E.right (A.completionRight y)) := by
                rw [hright y]
        _ = E.right
              (dotContragredient (completionLeftEquiv f g)
                (A.completionRight y)) :=
            embeddedCompletionAmbientAutomorphism_right
              E f g (A.completionRight y)
        _ = E.right (A.completionRight (g y)) := by
            have h :=
              completionAutomorphism_right_completion A f g hpair y
            exact congrArg E.right h
        _ = j.right (g y) := hright (g y)
  · exact embeddedCompletionAmbientAutomorphism_refl_left E
  · exact embeddedCompletionAmbientAutomorphism_refl_right E
  · intro f₁ f₂ g₁ g₂
    exact embeddedCompletionAmbientAutomorphism_comp_left
      E f₁ f₂ g₁ g₂
  · intro f₁ f₂ g₁ g₂
    exact embeddedCompletionAmbientAutomorphism_comp_right
      E f₁ f₂ g₁ g₂

end BananaMatrixStructure

end SuccessorTree.NonPrecompact
