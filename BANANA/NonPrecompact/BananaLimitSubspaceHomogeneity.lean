import BANANA.NonPrecompact.BananaLimitGlobalHomogeneity
import BANANA.NonPrecompact.BananaLimitFiniteAge

/-!
# Homogeneity for arbitrary finite two-sorted subspaces of BANANA

The preceding terminal theorem uses finite standard-coordinate source
presentations. Here we deduce the intrinsic formulation: every pair of
linear equivalences between two finite subspaces of the explicit
countable model that preserves their cross-pairing extends to a global
two-sorted pairing automorphism.

The proof represents the first pair of subspaces as the exact ranges of
an embedded finite BANANA structure. Transporting that embedding by the
two given linear equivalences gives a second embedding of the *same*
source structure, so global matrix-source homogeneity applies.
-/

namespace SuccessorTree.NonPrecompact

/-- Intrinsic, source-coordinate-free finite-substructure
ultrahomogeneity of the explicit countable BANANA pairing. -/
theorem bananaLimit_exists_global_pair_automorphism_extends_subspaces
    (U₁ U₂ V₁ V₂ : Submodule F2 BananaLimitVector)
    [Finite U₁] [Finite V₁]
    (fL : U₁ ≃ₗ[F2] U₂) (fR : V₁ ≃ₗ[F2] V₂)
    (hpair : ∀ u : U₁, ∀ v : V₁,
      bananaLimitPairing (fL u : BananaLimitVector)
        (fR v : BananaLimitVector) =
      bananaLimitPairing (u : BananaLimitVector)
        (v : BananaLimitVector)) :
    ∃ EL ER : BananaLimitVector ≃ₗ[F2] BananaLimitVector,
      (∀ x y : BananaLimitVector,
        bananaLimitPairing (EL x) (ER y) = bananaLimitPairing x y) ∧
      (∀ u : U₁, EL (u : BananaLimitVector) =
        (fL u : BananaLimitVector)) ∧
      (∀ v : V₁, ER (v : BananaLimitVector) =
        (fR v : BananaLimitVector)) := by
  classical
  obtain ⟨l, r, A, e₁, hrangeL, hrangeR⟩ :=
    exists_finite_banana_substructure_of_limit U₁ V₁
  let tL : (Fin l → F2) →ₗ[F2] U₁ :=
    e₁.left.codRestrict U₁ (by
      intro x
      rw [← hrangeL]
      exact ⟨x, rfl⟩)
  let tR : (Fin r → F2) →ₗ[F2] V₁ :=
    e₁.right.codRestrict V₁ (by
      intro y
      rw [← hrangeR]
      exact ⟨y, rfl⟩)
  let e₂ : BananaMatrixEmbeddingToLimit A := {
    left := U₂.subtype.comp (fL.toLinearMap.comp tL)
    right := V₂.subtype.comp (fR.toLinearMap.comp tR)
    left_injective := by
      intro x y h
      have h' : fL (tL x) = fL (tL y) :=
        Subtype.val_injective (show (fL (tL x) : BananaLimitVector) =
          (fL (tL y) : BananaLimitVector) from h)
      have ht : tL x = tL y := fL.injective h'
      exact e₁.left_injective (congrArg Subtype.val ht)
    right_injective := by
      intro x y h
      have h' : fR (tR x) = fR (tR y) :=
        Subtype.val_injective (show (fR (tR x) : BananaLimitVector) =
          (fR (tR y) : BananaLimitVector) from h)
      have ht : tR x = tR y := fR.injective h'
      exact e₁.right_injective (congrArg Subtype.val ht)
    pairing_apply := by
      intro x y
      change bananaLimitPairing
        (fL (tL x) : BananaLimitVector)
        (fR (tR y) : BananaLimitVector) = A.eval x y
      exact (hpair (tL x) (tR y)).trans
        (e₁.pairing_apply x y)
  }
  obtain ⟨EL, ER, hglobal, hleft, hright⟩ :=
    e₁.exists_global_pair_automorphism_extends e₂
  refine ⟨EL, ER, hglobal, ?_, ?_⟩
  · intro u
    have hu : (u : BananaLimitVector) ∈ LinearMap.range e₁.left := by
      rw [hrangeL]
      exact u.property
    obtain ⟨x, hx⟩ := hu
    calc
      EL (u : BananaLimitVector) =
          EL (e₁.left x) := by rw [hx]
      _ = e₂.left x := hleft x
      _ = (fL u : BananaLimitVector) := by
          change (fL (tL x) : BananaLimitVector) =
            (fL u : BananaLimitVector)
          have htu : tL x = u := Subtype.ext hx
          rw [htu]
  · intro v
    have hv : (v : BananaLimitVector) ∈ LinearMap.range e₁.right := by
      rw [hrangeR]
      exact v.property
    obtain ⟨y, hy⟩ := hv
    calc
      ER (v : BananaLimitVector) =
          ER (e₁.right y) := by rw [hy]
      _ = e₂.right y := hright y
      _ = (fR v : BananaLimitVector) := by
          change (fR (tR y) : BananaLimitVector) =
            (fR v : BananaLimitVector)
          have htv : tR y = v := Subtype.ext hy
          rw [htv]

end SuccessorTree.NonPrecompact
