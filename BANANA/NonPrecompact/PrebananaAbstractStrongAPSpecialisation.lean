import BANANA.NonPrecompact.PrebananaCanonicalFaithfulCodes
import BANANA.NonPrecompact.PrebananaAbstractCodeParity

/-!
# Abstract finite pre-BANANA strong amalgamation from encoded maps

Every nontrivial finite Boolean parity structure has a canonical
faithful marked atom code. Hence the generic coded strong-amalgamation
theorem applies immediately once the two abstract input embeddings
have been translated into natural marked atom embeddings.

The conclusion has a finite marked powerset amalgam; both maps from
the *original* Boolean algebras preserve injectivity, 0, 1, joins,
meets and the additive parity. They commute over the original
source, and their exact intersection is the common source image.

The remaining final bridge is to obtain the two encoded input maps
automatically from arbitrary abstract Boolean embeddings; the
separately staged encoded-naturality theorem supplies these.
-/

namespace SuccessorTree.NonPrecompact

/-- Full marked finite strong-amalgamation conclusion, assuming
that the two given Boolean embeddings have been represented
naturally by marked atom maps between canonical finite codes. -/
theorem prebananaAbstractStrongAmalgam_of_encodedMaps
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
    (f : PrebananaAtomEmbedding
      (prebananaAbstractAtomCode α μA hzeroA htopA haddA)
      (prebananaAbstractAtomCode β μB hzeroB htopB haddB))
    (g : PrebananaAtomEmbedding
      (prebananaAbstractAtomCode α μA hzeroA htopA haddA)
      (prebananaAbstractAtomCode γ μC hzeroC htopC haddC))
    (hφ : ∀ x : α,
      prebananaBooleanMap f (prebananaAbstractBooleanCode α x) =
        prebananaAbstractBooleanCode β (φ x))
    (hψ : ∀ x : α,
      prebananaBooleanMap g (prebananaAbstractBooleanCode α x) =
        prebananaAbstractBooleanCode γ (ψ x)) :
    ∃ D : PrebananaAtomStructure,
      ∃ FB : PrebananaMarkedFiniteMap β D μB,
      ∃ FC : PrebananaMarkedFiniteMap γ D μC,
        (∀ x : α, FB.toFun (φ x) = FC.toFun (ψ x)) ∧
        (∀ b : β, ∀ c : γ,
          FB.toFun b = FC.toFun c →
          ∃ a : α, φ a = b ∧ ψ a = c) := by
  exact prebananaFaithfulCodes_exists_strongAmalgam
    (prebananaAbstractAtomCode α μA hzeroA htopA haddA)
    (prebananaAbstractAtomCode β μB hzeroB htopB haddB)
    (prebananaAbstractAtomCode γ μC hzeroC htopC haddC)
    μA μB μC
    (prebananaCanonicalFaithfulFiniteCode α μA hzeroA htopA haddA)
    (prebananaCanonicalFaithfulFiniteCode β μB hzeroB htopB haddB)
    (prebananaCanonicalFaithfulFiniteCode γ μC hzeroC htopC haddC)
    φ ψ f g hφ hψ

end SuccessorTree.NonPrecompact
