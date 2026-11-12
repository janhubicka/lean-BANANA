import BANANA.NonPrecompact.BananaMatrixCoherentOneClass

/-!
# Coherence across distinct isomorphism classes

An isomorphism connects objects in one class. Applying the one-class
construction for each class gives a single class-indexed coherent
assignment into ONE ambient perfect-pair automorphism group. This result
is conditional on the class representatives and their embeddings; it
does not construct finite subspace presentations of actual substructures.
-/

namespace SuccessorTree.NonPrecompact

/-- A coherent extension family with all arrows landing in the same
perfect witness. Classifying the actual substructures is still required
before this gives the full circulation coherent-EPPA statement. -/
theorem exists_bananaMatrixCoherentClassFamily
    {I : Type*} (O : I → Type*)
    (l r : I → ℕ)
    (dL dR : ∀ c : I, O c → ℕ)
    (A : ∀ c : I, BananaMatrixStructure (l c) (r c))
    (B : ∀ (c : I) (U : O c),
      BananaMatrixStructure (dL c U) (dR c U))
    {n : ℕ}
    (h : ∀ c, l c + r c ≤ n)
    (j₀ : ∀ c, BananaMatrixEmbedding (A c) (perfectBanana n))
    (i : ∀ c (U : O c), BananaMatrixIso (A c) (B c U))
    (j : ∀ c (U : O c),
      BananaMatrixEmbedding (B c U) (perfectBanana n)) :
    ∃ Θ : ∀ (c : I) ⦃U V : O c⦄,
      BananaMatrixIso (B c U) (B c V) →
        BananaMatrixAutGroup (perfectBanana n),
      (∀ (c : I) (U : O c),
        Θ c (BananaMatrixIso.refl (B c U)) = 1) ∧
      (∀ (c : I) (U V W : O c)
          (p : BananaMatrixIso (B c U) (B c V))
          (q : BananaMatrixIso (B c V) (B c W)),
        Θ c q * Θ c p = Θ c (p.trans q)) ∧
      (∀ (c : I) (U V : O c)
          (p : BananaMatrixIso (B c U) (B c V)),
        (Θ c p)⁻¹ = Θ c p.symm) ∧
      (∀ (c : I) (U V : O c)
          (p : BananaMatrixIso (B c U) (B c V)),
        (∀ x, (Θ c p).1.1 ((j c U).left x) =
          (j c V).left (p.left x)) ∧
        (∀ y, (Θ c p).1.2 ((j c U).right y) =
          (j c V).right (p.right y))) := by
  classical
  let choices (c : I) :=
    exists_bananaMatrixCoherentOneClass
      (A c) (B c) (h c) (j₀ c) (i c) (j c)
  let Θc (c : I) := Classical.choose (choices c)
  have hΘc (c : I) := Classical.choose_spec (choices c)
  refine ⟨(fun c => Θc c), ?_, ?_, ?_, ?_⟩
  · intro c U
    exact (hΘc c).1 U
  · intro c U V W p q
    exact (hΘc c).2.1 U V W p q
  · intro c U V p
    exact (hΘc c).2.2.1 U V p
  · intro c U V p
    exact (hΘc c).2.2.2 U V p

end SuccessorTree.NonPrecompact
