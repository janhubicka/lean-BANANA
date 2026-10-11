import BANANA.NonPrecompact.PrebananaPowersetStrongAmalgam

/-!
# Strong intersection transported through Boolean atom representations

The finite marked-powerset strong-amalgamation theorem is already
kernel-verified. This module isolates the abstract-algebraic diagram
chase that transports its commuting square and strong intersection
property back to arbitrary original carriers.

The input consists of actual finite marked atom structures, genuine
atom embeddings, and Boolean-element codes that are natural with
the given abstract maps. The source code must be surjective, and
the two target codes injective. No particular choice of atom
enumeration is required.

Checking that those coded maps preserve all original Boolean
operations and parity is a separate interface; the point of this
lemma is the exact strong-amalgamation diagram.
-/

namespace SuccessorTree.NonPrecompact

/-- Coded strong amalgamation: given the naturality of the input
Boolean maps and faithful finite-subset codes, the powerset
strong amalgam induces a commuting square on the original
carriers, with exact common-image intersection. -/
theorem prebananaStrongIntersection_of_codedDiagram
    {α β γ : Type*}
    (A B C : PrebananaAtomStructure)
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (codeA : α → Finset (Fin A.atomCount))
    (codeB : β → Finset (Fin B.atomCount))
    (codeC : γ → Finset (Fin C.atomCount))
    (hA : Function.Surjective codeA)
    (hB : Function.Injective codeB)
    (hC : Function.Injective codeC)
    (φ : α → β) (ψ : α → γ)
    (hφ : ∀ a : α,
      prebananaBooleanMap f (codeA a) = codeB (φ a))
    (hψ : ∀ a : α,
      prebananaBooleanMap g (codeA a) = codeC (ψ a)) :
    ∃ D : PrebananaAtomStructure,
      ∃ u : PrebananaAtomEmbedding B D,
      ∃ v : PrebananaAtomEmbedding C D,
        (∀ a : α,
          prebananaBooleanMap u (codeB (φ a)) =
            prebananaBooleanMap v (codeC (ψ a))) ∧
        (∀ b : β, ∀ c : γ,
          prebananaBooleanMap u (codeB b) =
            prebananaBooleanMap v (codeC c) →
          ∃ a : α, φ a = b ∧ ψ a = c) := by
  classical
  obtain ⟨D, u, v, hcommute, hintersect⟩ :=
    exists_prebananaPowersetStrongAmalgam f g
  refine ⟨D, u, v, ?_, ?_⟩
  · intro a
    calc
      prebananaBooleanMap u (codeB (φ a)) =
          prebananaBooleanMap u (prebananaBooleanMap f (codeA a)) := by
            rw [hφ a]
      _ = prebananaBooleanMap v
            (prebananaBooleanMap g (codeA a)) :=
        hcommute (codeA a)
      _ = prebananaBooleanMap v (codeC (ψ a)) := by
        rw [hψ a]
  · intro b c hbc
    obtain ⟨r, hrB, hrC⟩ :=
      hintersect (codeB b) (codeC c) hbc
    obtain ⟨a, ha⟩ := hA r
    refine ⟨a, ?_, ?_⟩
    · apply hB
      calc
        codeB (φ a) = prebananaBooleanMap f (codeA a) :=
          (hφ a).symm
        _ = prebananaBooleanMap f r := by rw [ha]
        _ = codeB b := hrB
    · apply hC
      calc
        codeC (ψ a) = prebananaBooleanMap g (codeA a) :=
          (hψ a).symm
        _ = prebananaBooleanMap g r := by rw [ha]
        _ = codeC c := hrC

end SuccessorTree.NonPrecompact
