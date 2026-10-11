import BANANA.NonPrecompact.PrebananaAbstractAtomCodes
import BANANA.NonPrecompact.PrebananaAbstractMarkedPartitions
import BANANA.NonPrecompact.PrebananaReindexPartition
import BANANA.NonPrecompact.PrebananaAbstractAtomsLiteral

/-!
# Converting actual finite Boolean embeddings to marked Fin-atom embeddings

Every nontrivial finite Boolean parity structure has a concrete
Fin-indexed atom code. The abstract embedding partitions its target
atoms into nonempty source fibres, respecting their parity totals.
The reindexing theorem transports those fibre totals to the codes.

This supplies genuine `PrebananaAtomEmbedding` data for an arbitrary
parity-preserving finite Boolean-algebra embedding. The next interface
must establish naturality of the Boolean-element maps and transport
the existing strong-amalgamation diagram.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- An arbitrary finite Boolean-algebra embedding preserving the
additive F₂ parity induces a genuine atom embedding between the
Fin-indexed marked codes. The partition is recorded explicitly
on the original abstract atom sets. -/
theorem prebananaAbstractEmbedding_exists_encodedAtomEmbedding
    (α β : Type*)
    [BooleanAlgebra α] [Fintype α] [Nontrivial α]
    [BooleanAlgebra β] [Fintype β] [Nontrivial β]
    (μA : α → F2) (μB : β → F2)
    (hzeroA : μA ⊥ = 0)
    (htopA : μA ⊤ = 0)
    (haddA : ∀ x y : α, x ⊓ y = ⊥ →
      μA (x ⊔ y) = μA x + μA y)
    (hzeroB : μB ⊥ = 0)
    (htopB : μB ⊤ = 0)
    (haddB : ∀ x y : β, x ⊓ y = ⊥ →
      μB (x ⊔ y) = μB x + μB y)
    (φ : α → β)
    (hinj : Function.Injective φ)
    (hbot : φ ⊥ = ⊥)
    (htop : φ ⊤ = ⊤)
    (hsup : ∀ x y : α, φ (x ⊔ y) = φ x ⊔ φ y)
    (hinf : ∀ x y : α, φ (x ⊓ y) = φ x ⊓ φ y)
    (hmark : ∀ x : α, μB (φ x) = μA x) :
    ∃ f : PrebananaAtomEmbedding
        (prebananaAbstractAtomCode α μA hzeroA htopA haddA)
        (prebananaAbstractAtomCode β μB hzeroB htopB haddB),
      ∃ part : PrebananaAbstractAtoms β → PrebananaAbstractAtoms α,
        Function.Surjective part ∧
        (∀ j : Fin (Fintype.card (PrebananaAbstractAtoms β)),
          f.part j =
            prebananaReindexedPart
              (prebananaAbstractAtomIndex α)
              (prebananaAbstractAtomIndex β)
              part j) ∧
        (∀ s : Finset (PrebananaAbstractAtoms α),
          prebananaAbstractPowersetMap φ s =
            Finset.univ.filter (fun b => part b ∈ s)) := by
  classical
  obtain ⟨part, hsurj, hpow, hfibre⟩ :=
    prebananaAbstractEmbedding_exists_literalMarkedAtomPartition
      α β μA μB hzeroB haddB φ hinj hbot htop hsup hinf hmark
  let eA := prebananaAbstractAtomIndex α
  let eB := prebananaAbstractAtomIndex β
  let q := prebananaReindexedPart eA eB part
  let E : PrebananaAtomEmbedding
      (prebananaAbstractAtomCode α μA hzeroA htopA haddA)
      (prebananaAbstractAtomCode β μB hzeroB htopB haddB) := {
    part := q
    fibre_nonempty := by
      intro a
      obtain ⟨b, hb⟩ :=
        prebananaReindexedPart_surjective eA eB part hsurj a
      exact ⟨b, by simpa [prebananaFiber, q] using hb⟩
    fibre_mark_parity := by
      intro a
      rw [prebananaMarkedCount_cast_eq_sum]
      have hsum :=
        prebananaReindexedPart_fibre_mark
          eA eB part
          (fun x : PrebananaAbstractAtoms α => μA (x : α))
          (fun y : PrebananaAbstractAtoms β => μB (y : β))
          hfibre a
      change
        (∑ j ∈
          (Finset.univ :
            Finset (Fin (Fintype.card (PrebananaAbstractAtoms β)))).filter
            (fun j => prebananaReindexedPart eA eB part j = a),
          μB ((prebananaFiniteBooleanAtomFinsetOrderIso β).symm
            ({eB j} : Finset (PrebananaAbstractAtoms β)))) =
        μA ((prebananaFiniteBooleanAtomFinsetOrderIso α).symm
          ({eA a} : Finset (PrebananaAbstractAtoms α)))
      simpa only [prebananaFiniteBoolean_singleton_represents_atom]
        using hsum
  }
  refine ⟨E, part, hsurj, ?_, hpow⟩
  intro j
  rfl

end SuccessorTree.NonPrecompact
