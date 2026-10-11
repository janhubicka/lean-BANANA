import BANANA.NonPrecompact.PrebananaAbstractEncodedNaturality
import BANANA.NonPrecompact.PrebananaAbstractStrongAPSpecialisation

/-!
# Strong amalgamation for arbitrary finite pre-BANANA Boolean structures

This theorem closes the algebraic strong-amalgamation step in the
circulation proof. Its source objects are arbitrary nontrivial
finite Boolean algebras, each carrying a disjoint-additive
F₂-valued marking that vanishes at bottom and top. The two input
maps are injective, preserve the bounded-lattice operations,
and preserve the markings.

The target is the finite Boolean powerset of a marked atom
structure. Both resulting maps preserve the same bounded-lattice
operations and parity, commute over the original source and
intersect exactly in its image.

The theorem is an algebraic strong-amalgamation statement. General
Fraïssé existence and the Ryll–Nardzewski omega-categoricity
deduction are standard external results, not claims of this module.
-/

namespace SuccessorTree.NonPrecompact

/-- Strong amalgamation of two arbitrary embeddings of nontrivial
finite Boolean algebras with disjoint-additive F₂ parity. The
target is a concrete finite marked powerset Boolean algebra. -/
theorem prebananaAbstractFiniteStrongAmalgamation
    (α β γ : Type*)
    [BooleanAlgebra α] [Fintype α] [Nontrivial α]
    [BooleanAlgebra β] [Fintype β] [Nontrivial β]
    [BooleanAlgebra γ] [Fintype γ] [Nontrivial γ]
    (μA : α → F2) (μB : β → F2) (μC : γ → F2)
    (hzeroA : μA ⊥ = 0) (htopA : μA ⊤ = 0)
    (haddA : ∀ x y : α, x ⊓ y = ⊥ →
      μA (x ⊔ y) = μA x + μA y)
    (hzeroB : μB ⊥ = 0) (htopB : μB ⊤ = 0)
    (haddB : ∀ x y : β, x ⊓ y = ⊥ →
      μB (x ⊔ y) = μB x + μB y)
    (hzeroC : μC ⊥ = 0) (htopC : μC ⊤ = 0)
    (haddC : ∀ x y : γ, x ⊓ y = ⊥ →
      μC (x ⊔ y) = μC x + μC y)
    (φ : α → β) (ψ : α → γ)
    (hinjφ : Function.Injective φ)
    (hbotφ : φ ⊥ = ⊥) (htopφ : φ ⊤ = ⊤)
    (hsupφ : ∀ x y : α, φ (x ⊔ y) = φ x ⊔ φ y)
    (hinfφ : ∀ x y : α, φ (x ⊓ y) = φ x ⊓ φ y)
    (hmarkφ : ∀ x : α, μB (φ x) = μA x)
    (hinjψ : Function.Injective ψ)
    (hbotψ : ψ ⊥ = ⊥) (htopψ : ψ ⊤ = ⊤)
    (hsupψ : ∀ x y : α, ψ (x ⊔ y) = ψ x ⊔ ψ y)
    (hinfψ : ∀ x y : α, ψ (x ⊓ y) = ψ x ⊓ ψ y)
    (hmarkψ : ∀ x : α, μC (ψ x) = μA x) :
    ∃ D : PrebananaAtomStructure,
      ∃ FB : PrebananaMarkedFiniteMap β D μB,
      ∃ FC : PrebananaMarkedFiniteMap γ D μC,
        (∀ x : α, FB.toFun (φ x) = FC.toFun (ψ x)) ∧
        (∀ b : β, ∀ c : γ,
          FB.toFun b = FC.toFun c →
          ∃ a : α, φ a = b ∧ ψ a = c) := by
  obtain ⟨f, hf⟩ :=
    prebananaAbstractEmbedding_exists_encodedBooleanMap
      α β μA μB hzeroA htopA haddA hzeroB htopB haddB
      φ hinjφ hbotφ htopφ hsupφ hinfφ hmarkφ
  obtain ⟨g, hg⟩ :=
    prebananaAbstractEmbedding_exists_encodedBooleanMap
      α γ μA μC hzeroA htopA haddA hzeroC htopC haddC
      ψ hinjψ hbotψ htopψ hsupψ hinfψ hmarkψ
  exact prebananaAbstractStrongAmalgam_of_encodedMaps
    α β γ μA μB μC
    hzeroA htopA haddA
    hzeroB htopB haddB
    hzeroC htopC haddC
    φ ψ f g hf hg

end SuccessorTree.NonPrecompact
