import BANANA.NonPrecompact.BananaLimitFinitePairHomogeneity
import BANANA.NonPrecompact.BananaLimitBlockPairLift

/-!
# Ultrahomogeneity of the explicit countable BANANA pairing

Every pair of embeddings of the same finite matrix presentation into
the countable finitely supported rational-coordinate pairing is carried
one to the other by a global two-sorted linear pairing automorphism.

Proof architecture:
1. collect finite supports and factor through one perfect coordinate block;
2. apply the already verified homogeneity of that finite perfect pair;
3. turn the finite self-embedding into two linear equivalences;
4. lift the two block equivalences by the identity outside the block.

This is the coordinate-embedding form of Fraïssé homogeneity. The
model-theoretic orbit-finiteness/omega-categoricity consequence is not
asserted in this module.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

namespace BananaMatrixEmbeddingToLimit

/-- Every two embeddings of one finite BANANA pairing into the explicit
countable pairing are conjugate by a global pairing-preserving pair of
linear equivalences. This is pointwise extension on both sorts. -/
theorem exists_global_pair_automorphism_extends
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (e₁ e₂ : BananaMatrixEmbeddingToLimit A) :
    ∃ EL ER : BananaLimitVector ≃ₗ[F2] BananaLimitVector,
      (∀ x y : BananaLimitVector,
        bananaLimitPairing (EL x) (ER y) = bananaLimitPairing x y) ∧
      (∀ x, EL (e₁.left x) = e₂.left x) ∧
      (∀ y, ER (e₁.right y) = e₂.right y) := by
  classical
  obtain ⟨S, f₁, f₂, H, h₁L, h₁R, h₂L, h₂R, hL, hR⟩ :=
    exists_finite_perfect_ambient_automorphism e₁ e₂
  let E := bananaLimitBlockStandardEquiv S
  let rightEquiv :
      (Fin S.card → F2) ≃ₗ[F2] (Fin S.card → F2) :=
    LinearEquiv.ofBijective H.right
      ⟨H.right_injective,
        Finite.injective_iff_surjective.mp H.right_injective⟩
  let leftBlock : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S :=
    (E.symm.trans H.leftSelfEquiv).trans E
  let rightBlock : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S :=
    (E.symm.trans rightEquiv).trans E

  have hfinite (x y : Fin S.card → F2) :
      H.leftSelfEquiv x ⬝ᵥ rightEquiv y = x ⬝ᵥ y := by
    change H.left x ⬝ᵥ H.right y = x ⬝ᵥ y
    simpa only [perfectBanana_eval] using H.pairing_apply x y

  have hpair (u v : bananaLimitBlock S) :
      bananaLimitPairing (leftBlock u : BananaLimitVector)
        (rightBlock v : BananaLimitVector) =
      bananaLimitPairing (u : BananaLimitVector)
        (v : BananaLimitVector) := by
    change bananaLimitPairing
      (E (H.leftSelfEquiv (E.symm u)) : BananaLimitVector)
      (E (rightEquiv (E.symm v)) : BananaLimitVector) =
      bananaLimitPairing (u : BananaLimitVector) (v : BananaLimitVector)
    calc
      bananaLimitPairing
          (E (H.leftSelfEquiv (E.symm u)) : BananaLimitVector)
          (E (rightEquiv (E.symm v)) : BananaLimitVector) =
        H.leftSelfEquiv (E.symm u) ⬝ᵥ
          rightEquiv (E.symm v) :=
        bananaLimitBlockStandardEquiv_pairing S _ _
      _ = (E.symm u) ⬝ᵥ (E.symm v) := hfinite _ _
      _ = bananaLimitPairing (u : BananaLimitVector)
          (v : BananaLimitVector) := by
          have h :=
            (bananaLimitBlockStandardEquiv_pairing S
              (E.symm u) (E.symm v)).symm
          change (E.symm u) ⬝ᵥ (E.symm v) =
            bananaLimitPairing
              (E (E.symm u) : BananaLimitVector)
              (E (E.symm v) : BananaLimitVector) at h
          simpa only [LinearEquiv.apply_symm_apply] using h

  have hLblock (x : Fin l → F2) :
      leftBlock (E (f₁.left x)) = E (f₂.left x) := by
    simpa only [leftBlock, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply,
      BananaMatrixEmbedding.leftSelfEquiv_apply] using
      congrArg E (hL x)

  have hRblock (y : Fin r → F2) :
      rightBlock (E (f₁.right y)) = E (f₂.right y) := by
    have h : rightEquiv (f₁.right y) = f₂.right y := by
      change H.right (f₁.right y) = f₂.right y
      exact hR y
    simpa only [rightBlock, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply] using congrArg E h

  obtain ⟨EL, ER, hGlobal, hEL, hER⟩ :=
    exists_bananaLimit_global_pair_automorphism_of_block
      S leftBlock rightBlock hpair
  refine ⟨EL, ER, hGlobal, ?_, ?_⟩
  · intro x
    calc
      EL (e₁.left x) =
          EL (E (f₁.left x) : BananaLimitVector) := by
            simpa [bananaLimitBlockStandardEmbedding, E] using
              congrArg EL (h₁L x).symm
      _ = (leftBlock (E (f₁.left x)) : BananaLimitVector) :=
            hEL (E (f₁.left x))
      _ = (E (f₂.left x) : BananaLimitVector) :=
            congrArg Subtype.val (hLblock x)
      _ = e₂.left x := by
            simpa [bananaLimitBlockStandardEmbedding, E] using h₂L x
  · intro y
    calc
      ER (e₁.right y) =
          ER (E (f₁.right y) : BananaLimitVector) := by
            simpa [bananaLimitBlockStandardEmbedding, E] using
              congrArg ER (h₁R y).symm
      _ = (rightBlock (E (f₁.right y)) : BananaLimitVector) :=
            hER (E (f₁.right y))
      _ = (E (f₂.right y) : BananaLimitVector) :=
            congrArg Subtype.val (hRblock y)
      _ = e₂.right y := by
            simpa [bananaLimitBlockStandardEmbedding, E] using h₂R y

end BananaMatrixEmbeddingToLimit

end SuccessorTree.NonPrecompact
