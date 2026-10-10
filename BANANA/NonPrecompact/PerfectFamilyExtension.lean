import BANANA.NonPrecompact.PerfectHomogeneity

/-!
# Simultaneous extension of finitely many partial isomorphisms

In the proof that perfect total n-systems are cofinal, one first
completes the underlying finite BANANA structure to a common
perfect pairing. Each named partial isomorphism then extends to
a total automorphism of that same perfect completion, by perfect
pairing homogeneity.

The source of each partial isomorphism may have its own left and
right dimensions and pairing matrix. The ambient perfect pair is
common to the whole family. No compatibility between the
different named partial maps is required for this extension step.
-/

namespace SuccessorTree.NonPrecompact

/-- Any finite indexed family of pairs of embeddings of possibly
different source BANANA structures into the same perfect pair can be
matched by a family of automorphisms of that single perfect pair. -/
theorem exists_perfectPairAutomorphism_family_extends
    {n k : ℕ}
    (l r : Fin n → ℕ)
    (A : ∀ i : Fin n, BananaMatrixStructure (l i) (r i))
    (e₁ e₂ : ∀ i : Fin n,
      BananaMatrixEmbedding (A i) (perfectBanana k)) :
    ∃ H : Fin n →
        BananaMatrixEmbedding (perfectBanana k) (perfectBanana k),
      (∀ i (x : Fin (l i) → F2),
        (H i).left ((e₁ i).left x) = (e₂ i).left x) ∧
      (∀ i (y : Fin (r i) → F2),
        (H i).right ((e₁ i).right y) = (e₂ i).right y) := by
  classical
  let W (i : Fin n) :
      ∃ H : BananaMatrixEmbedding (perfectBanana k) (perfectBanana k),
        (∀ x, H.left ((e₁ i).left x) = (e₂ i).left x) ∧
        (∀ y, H.right ((e₁ i).right y) = (e₂ i).right y) :=
    exists_perfectPairAutomorphism_extends (e₁ i) (e₂ i)
  refine ⟨fun i => Classical.choose (W i), ?_, ?_⟩
  · intro i x
    exact (Classical.choose_spec (W i)).1 x
  · intro i y
    exact (Classical.choose_spec (W i)).2 y

end SuccessorTree.NonPrecompact
