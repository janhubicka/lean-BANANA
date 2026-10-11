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

/-- An atom partition conjugated through two finite enumerations
induces exactly the same Boolean map after transporting finite
subsets along the enumerations. This is the naturality identity
needed for the abstract strong-amalgamation diagram. -/
theorem prebananaReindexedBooleanMap_naturality
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (eI : Fin (Fintype.card I) ≃ I)
    (eJ : Fin (Fintype.card J) ≃ J)
    (part : J → I)
    (s : Finset (Fin (Fintype.card I))) :
    ((Finset.univ : Finset (Fin (Fintype.card J))).filter
      (fun j => prebananaReindexedPart eI eJ part j ∈ s)).image eJ =
    (Finset.univ : Finset J).filter
      (fun b => part b ∈ s.image eI) := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨j, hj, hbj⟩ := Finset.mem_image.mp hb
    have hjS : prebananaReindexedPart eI eJ part j ∈ s :=
      (Finset.mem_filter.mp hj).2
    have hbase : part (eJ j) ∈ s.image eI := by
      refine Finset.mem_image.mpr
        ⟨prebananaReindexedPart eI eJ part j, hjS, ?_⟩
      simp [prebananaReindexedPart]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by simpa [hbj] using hbase⟩
  · intro hb
    have hb' : part b ∈ s.image eI :=
      (Finset.mem_filter.mp hb).2
    obtain ⟨i, hi, hieq⟩ := Finset.mem_image.mp hb'
    have hq : prebananaReindexedPart eI eJ part (eJ.symm b) = i := by
      apply eI.injective
      simpa [prebananaReindexedPart] using hieq.symm
    refine Finset.mem_image.mpr
      ⟨eJ.symm b, ?_, by simp⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by simpa [hq] using hi⟩

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
      simp only [prebananaFiber, Finset.filter_nonempty_iff,
        Finset.mem_univ, true_and]
      exact ⟨b, hb⟩
    fibre_mark_parity := by
      intro a
      rw [prebananaMarkedCount_cast_eq_sum]
      have hsum :=
        prebananaReindexedPart_fibre_mark
          eA eB part
          (fun x : PrebananaAbstractAtoms α => μA (x : α))
          (fun y : PrebananaAbstractAtoms β => μB (y : β))
          hfibre a
      calc
        (∑ j ∈ prebananaFiber q a,
          (prebananaAbstractAtomCode β μB hzeroB htopB haddB).mark j) =
          ∑ j ∈ prebananaFiber q a, μB (eB j : β) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact congrArg μB
              (prebananaFiniteBoolean_singleton_represents_atom β (eB j))
        _ = μA (eA a : α) := by
          refine Eq.trans ?_ hsum
          apply Finset.sum_congr
          · ext j
            simp [prebananaFiber, q]
          · intro j hj
            rfl
        _ = (prebananaAbstractAtomCode α μA hzeroA htopA haddA).mark a := by
          exact (congrArg μA
            (prebananaFiniteBoolean_singleton_represents_atom α (eA a))).symm
  }
  refine ⟨E, part, hsurj, ?_, hpow⟩
  intro j
  rfl

end SuccessorTree.NonPrecompact
