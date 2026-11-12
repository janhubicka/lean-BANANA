import BANANA.NonPrecompact.BananaMatrixCoherentChoiceLemmas
import BANANA.NonPrecompact.BananaMatrixCoherentTransport

/-!
# Coherent extension assignment for one whole isomorphism class

Fix a representative A, a perfect ambient B_n, and copies of structures
isomorphic to A embedded in B_n. If l+r ≤ n, one assignment extends EVERY
isomorphism between the copies and preserves identity, composition and
inverse on both sorts. The representative homomorphism and conjugators are
constructed here from existing finite homogeneity and completion results.

The remaining class-wide task is to identify actual finite substructures
with their isomorphism-class coordinate presentations.
-/

namespace SuccessorTree.NonPrecompact

/-- Coherent extension for every isomorphism in a single class, within
one fixed perfect witness. Coordinate dimensions may differ definitionally. -/
theorem exists_bananaMatrixCoherentOneClass
    {O : Type*} {l r n : ℕ} {dL dR : O → ℕ}
    (A : BananaMatrixStructure l r)
    (B : ∀ U : O, BananaMatrixStructure (dL U) (dR U))
    (h : l + r ≤ n)
    (j₀ : BananaMatrixEmbedding A (perfectBanana n))
    (i : ∀ U : O, BananaMatrixIso A (B U))
    (j : ∀ U : O, BananaMatrixEmbedding (B U) (perfectBanana n)) :
    ∃ Θ : ∀ ⦃U V : O⦄,
        BananaMatrixIso (B U) (B V) →
          BananaMatrixAutGroup (perfectBanana n),
      (∀ U : O, Θ (BananaMatrixIso.refl (B U)) = 1) ∧
      (∀ (U V W : O)
          (p : BananaMatrixIso (B U) (B V))
          (q : BananaMatrixIso (B V) (B W)),
        Θ q * Θ p = Θ (p.trans q)) ∧
      (∀ (U V : O) (p : BananaMatrixIso (B U) (B V)),
        (Θ p)⁻¹ = Θ p.symm) ∧
      (∀ (U V : O) (p : BananaMatrixIso (B U) (B V)),
        (∀ x, (Θ p).1.1 ((j U).left x) = (j V).left (p.left x)) ∧
        (∀ y, (Θ p).1.2 ((j U).right y) = (j V).right (p.right y))) := by
  classical
  obtain ⟨ρ, hρ⟩ :=
    exists_bananaMatrixAlignedCompletionHom_of_le A j₀ h
  have hconj (U : O) :
      ∃ g : BananaMatrixAutGroup (perfectBanana n),
        (∀ x, g.1.1 (j₀.left x) = (j U).left ((i U).left x)) ∧
        (∀ y, g.1.2 (j₀.right y) = (j U).right ((i U).right y)) := by
    exact exists_bananaMatrixRepresentativeConjugator j₀ (j U) (i U)
  let g : O → BananaMatrixAutGroup (perfectBanana n) :=
    fun U => Classical.choose (hconj U)
  have hgL : ∀ (U : O) x,
      (g U).1.1 (j₀.left x) = (j U).left ((i U).left x) := by
    intro U x
    exact (Classical.choose_spec (hconj U)).1 x
  have hgR : ∀ (U : O) y,
      (g U).1.2 (j₀.right y) = (j U).right ((i U).right y) := by
    intro U y
    exact (Classical.choose_spec (hconj U)).2 y
  refine ⟨(fun {_ _} p => bananaMatrixCoherentTransport ρ g i p),
    ?_, ?_, ?_, ?_⟩
  · intro U
    exact bananaMatrixCoherentTransport_refl ρ g i U
  · intro U V W p q
    exact bananaMatrixCoherentTransport_trans ρ g i p q
  · intro U V p
    exact bananaMatrixCoherentTransport_symm ρ g i p
  · intro U V p
    exact bananaMatrixCoherentTransport_extends ρ g i j₀ j
      (fun f x => (hρ f).1 x)
      (fun f y => (hρ f).2 y) hgL hgR p

end SuccessorTree.NonPrecompact
