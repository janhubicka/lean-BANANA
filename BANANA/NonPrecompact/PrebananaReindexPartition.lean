import BANANA.NonPrecompact.PrebananaAmalgamBridge

/-!
# Transporting finite marked atom partitions through enumerations

The manuscript works with arbitrary finite atom sets, whereas the
`PrebananaAtomEmbedding` API uses `Fin n`. An atom partition and
its F₂ fibre-marking equations remain valid after enumerating
both the source and target atom sets with finite equivalences.

This lemma will transport the checked arbitrary-Boolean embedding
partitions to the concrete finite pre-BANANA category without changing
their markings.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- Conjugate an arbitrary atom partition through finite enumerations. -/
def prebananaReindexedPart
    {I J : Type*} [Fintype I] [Fintype J]
    (eI : Fin (Fintype.card I) ≃ I)
    (eJ : Fin (Fintype.card J) ≃ J)
    (part : J → I) :
    Fin (Fintype.card J) → Fin (Fintype.card I) :=
  fun j => eI.symm (part (eJ j))

/-- A surjective atom partition remains surjective after reindexing. -/
theorem prebananaReindexedPart_surjective
    {I J : Type*} [Fintype I] [Fintype J]
    (eI : Fin (Fintype.card I) ≃ I)
    (eJ : Fin (Fintype.card J) ≃ J)
    (part : J → I)
    (hsurj : Function.Surjective part) :
    Function.Surjective (prebananaReindexedPart eI eJ part) := by
  intro i
  obtain ⟨b, hb⟩ := hsurj (eI i)
  refine ⟨eJ.symm b, ?_⟩
  simp [prebananaReindexedPart, hb]

/-- Reindexing preserves each individual fibre sum, not merely the
total sum of all marks. -/
theorem prebananaReindexedPart_fibre_sum
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (eI : Fin (Fintype.card I) ≃ I)
    (eJ : Fin (Fintype.card J) ≃ J)
    (part : J → I)
    (markJ : J → F2)
    (i : Fin (Fintype.card I)) :
    (∑ j ∈ (Finset.univ : Finset (Fin (Fintype.card J))).filter
        (fun j => prebananaReindexedPart eI eJ part j = i),
      markJ (eJ j)) =
    ∑ b ∈ (Finset.univ : Finset J).filter
        (fun b => part b = eI i), markJ b := by
  classical
  have hpred (j : Fin (Fintype.card J)) :
      (prebananaReindexedPart eI eJ part j = i) ↔
        part (eJ j) = eI i := by
    constructor
    · intro h
      have hh := congrArg eI h
      simpa [prebananaReindexedPart] using hh
    · intro h
      simp [prebananaReindexedPart, h]
  have hsum :=
    Fintype.sum_equiv eJ
      (fun j : Fin (Fintype.card J) =>
        if prebananaReindexedPart eI eJ part j = i
        then markJ (eJ j) else 0)
      (fun b : J =>
        if part b = eI i then markJ b else 0)
      (by
        intro j
        simp only [hpred j])
  simpa only [Finset.sum_filter] using hsum

/-- In particular, an F₂-mark-preserving partition stays
mark-preserving in the `Fin n` coordinates. -/
theorem prebananaReindexedPart_fibre_mark
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (eI : Fin (Fintype.card I) ≃ I)
    (eJ : Fin (Fintype.card J) ≃ J)
    (part : J → I)
    (markI : I → F2) (markJ : J → F2)
    (hmark : ∀ a : I,
      (∑ b ∈ (Finset.univ : Finset J).filter
          (fun b => part b = a), markJ b) = markI a)
    (i : Fin (Fintype.card I)) :
    (∑ j ∈ (Finset.univ : Finset (Fin (Fintype.card J))).filter
        (fun j => prebananaReindexedPart eI eJ part j = i),
      markJ (eJ j)) = markI (eI i) := by
  exact (prebananaReindexedPart_fibre_sum eI eJ part markJ i).trans
    (hmark (eI i))

end SuccessorTree.NonPrecompact
