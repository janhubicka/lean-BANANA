import BANANA.NonPrecompact.PrebananaAbstractStrongIntersectionTransfer
import BANANA.NonPrecompact.PrebananaCodedBooleanEmbedding

/-!
# Strong amalgamation of faithful finite Boolean encodings

Finite pre-BANANA amalgamation has two logically separate pieces:
the marked powerset embeddings preserve Boolean operations and parity,
and the common image of the two Boolean subalgebras is exactly the
source image. The preceding modules verify those pieces separately.

Here a faithful code is an injective, surjective representation of
an abstract Boolean algebra in the finite marked powerset, preserving
the bounded lattice operations and the additive F₂ marking. A map of
such codes is natural when the given abstract map is exactly the
Boolean map induced by the corresponding marked atom embedding.

This theorem packages a genuine finite marked powerset amalgam,
two injective bounded-lattice and marking-preserving maps from the
original carriers, commutativity, and exact common-image intersection.
The next step instantiates these hypotheses using the canonical
abstract Boolean atom codes.
-/

namespace SuccessorTree.NonPrecompact

/-- An abstract Boolean algebra represented faithfully by the
finite powerset of a marked atom structure, together with the
parity map of its original elements. -/
structure PrebananaFaithfulFiniteCode
    (β : Type*) [BooleanAlgebra β]
    (B : PrebananaAtomStructure) (μ : β → F2) where
  toFun : β → Finset (Fin B.atomCount)
  injective : Function.Injective toFun
  surjective : Function.Surjective toFun
  map_bot : toFun ⊥ = ∅
  map_top : toFun ⊤ = Finset.univ
  map_sup : ∀ x y : β, toFun (x ⊔ y) = toFun x ∪ toFun y
  map_inf : ∀ x y : β, toFun (x ⊓ y) = toFun x ∩ toFun y
  map_parity : ∀ x : β, prebananaBooleanParity B (toFun x) = μ x

/-- An injective parity-preserving bounded-lattice map into a
finite marked powerset. Boolean complements are determined
uniquely by the bounded-lattice operations. -/
structure PrebananaMarkedFiniteMap
    (β : Type*) [BooleanAlgebra β]
    (D : PrebananaAtomStructure) (μ : β → F2) where
  toFun : β → Finset (Fin D.atomCount)
  injective : Function.Injective toFun
  map_bot : toFun ⊥ = ∅
  map_top : toFun ⊤ = Finset.univ
  map_sup : ∀ x y : β, toFun (x ⊔ y) = toFun x ∪ toFun y
  map_inf : ∀ x y : β, toFun (x ⊓ y) = toFun x ∩ toFun y
  map_parity : ∀ x : β, prebananaBooleanParity D (toFun x) = μ x

/-- A strong amalgamation diagram of finite marked atom structures
transfers to any faithful finite codes that are natural for the
original Boolean-algebra maps. This includes both genuine
marked embeddings and *exact* common-image intersection. -/
theorem prebananaFaithfulCodes_exists_strongAmalgam
    {α β γ : Type*}
    [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ]
    (A B C : PrebananaAtomStructure)
    (μA : α → F2) (μB : β → F2) (μC : γ → F2)
    (CA : PrebananaFaithfulFiniteCode α A μA)
    (CB : PrebananaFaithfulFiniteCode β B μB)
    (CC : PrebananaFaithfulFiniteCode γ C μC)
    (φ : α → β) (ψ : α → γ)
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (hφ : ∀ a : α,
      prebananaBooleanMap f (CA.toFun a) = CB.toFun (φ a))
    (hψ : ∀ a : α,
      prebananaBooleanMap g (CA.toFun a) = CC.toFun (ψ a)) :
    ∃ D : PrebananaAtomStructure,
      ∃ hB : PrebananaMarkedFiniteMap β D μB,
      ∃ hC : PrebananaMarkedFiniteMap γ D μC,
        (∀ a : α, hB.toFun (φ a) = hC.toFun (ψ a)) ∧
        (∀ b : β, ∀ c : γ,
          hB.toFun b = hC.toFun c →
          ∃ a : α, φ a = b ∧ ψ a = c) := by
  classical
  obtain ⟨D, u, v, hcommute, hstrong⟩ :=
    prebananaStrongIntersection_of_codedDiagram
      A B C f g CA.toFun CB.toFun CC.toFun
      CA.surjective CB.injective CC.injective
      φ ψ hφ hψ
  obtain ⟨hB, hBeq, hBinj, hBbot, hBtop, hBsup, hBinf, hBmark⟩ :=
    prebananaCodedBooleanEmbedding_properties B D u
      CB.toFun μB CB.injective CB.map_bot CB.map_top
      CB.map_sup CB.map_inf CB.map_parity
  obtain ⟨hC, hCeq, hCinj, hCbot, hCtop, hCsup, hCinf, hCmark⟩ :=
    prebananaCodedBooleanEmbedding_properties C D v
      CC.toFun μC CC.injective CC.map_bot CC.map_top
      CC.map_sup CC.map_inf CC.map_parity
  let FB : PrebananaMarkedFiniteMap β D μB := {
    toFun := hB
    injective := hBinj
    map_bot := hBbot
    map_top := hBtop
    map_sup := hBsup
    map_inf := hBinf
    map_parity := hBmark
  }
  let FC : PrebananaMarkedFiniteMap γ D μC := {
    toFun := hC
    injective := hCinj
    map_bot := hCbot
    map_top := hCtop
    map_sup := hCsup
    map_inf := hCinf
    map_parity := hCmark
  }
  refine ⟨D, FB, FC, ?_, ?_⟩
  · intro a
    change hB (φ a) = hC (ψ a)
    calc
      hB (φ a) = prebananaBooleanMap u (CB.toFun (φ a)) :=
        hBeq _
      _ = prebananaBooleanMap v (CC.toFun (ψ a)) :=
        hcommute a
      _ = hC (ψ a) := (hCeq _).symm
  · intro b c hbc
    change hB b = hC c at hbc
    apply hstrong b c
    calc
      prebananaBooleanMap u (CB.toFun b) = hB b :=
        (hBeq _).symm
      _ = hC c := hbc
      _ = prebananaBooleanMap v (CC.toFun c) := hCeq _

end SuccessorTree.NonPrecompact
