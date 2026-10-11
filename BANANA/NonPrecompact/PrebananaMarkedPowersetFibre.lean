import BANANA.NonPrecompact.PrebananaPowersetBridge

/-!
# Recovering fibre parity from preservation of Boolean parity

Suppose a map on finite Boolean powersets is inverse image
along a map of atom indices. If the Boolean map preserves the
additive F₂ marking on every Boolean element, then each atom
fibre has exactly its required parity.

In particular, a surjective atom partition whose induced
powerset map preserves parity is a genuine pre-BANANA embedding.
This is the marking-preservation step required by the abstract
embedding-to-atom presentation bridge.
-/

namespace SuccessorTree.NonPrecompact

/-- Marking preservation on arbitrary Boolean elements implies
the exact marking condition on every atom fibre. -/
theorem prebanana_fibre_mark_parity_of_booleanMap
    {A B : PrebananaAtomStructure}
    (F : Finset (Fin A.atomCount) → Finset (Fin B.atomCount))
    (part : Fin B.atomCount → Fin A.atomCount)
    (hmap : ∀ s : Finset (Fin A.atomCount),
      F s = Finset.univ.filter (fun b => part b ∈ s))
    (hparity : ∀ s : Finset (Fin A.atomCount),
      prebananaBooleanParity B (F s) =
        prebananaBooleanParity A s)
    (a : Fin A.atomCount) :
    (prebananaMarkedCount B.mark (prebananaFiber part a) : F2) =
      A.mark a := by
  classical
  have hF : F {a} = prebananaFiber part a := by
    simpa [prebananaFiber] using hmap ({a} : Finset (Fin A.atomCount))
  have h := hparity ({a} : Finset (Fin A.atomCount))
  rw [hF] at h
  simpa [prebananaBooleanParity, prebananaMarkedCount_cast_eq_sum] using h

/-- A surjective atom-partition map, whose induced Boolean map
preserves the parity predicate, is a genuine marked embedding. -/
theorem prebanana_exists_markedEmbedding_of_booleanMap
    {A B : PrebananaAtomStructure}
    (F : Finset (Fin A.atomCount) → Finset (Fin B.atomCount))
    (part : Fin B.atomCount → Fin A.atomCount)
    (hsurj : Function.Surjective part)
    (hmap : ∀ s : Finset (Fin A.atomCount),
      F s = Finset.univ.filter (fun b => part b ∈ s))
    (hparity : ∀ s : Finset (Fin A.atomCount),
      prebananaBooleanParity B (F s) =
        prebananaBooleanParity A s) :
    ∃ f : PrebananaAtomEmbedding A B,
      ∀ s : Finset (Fin A.atomCount),
        prebananaBooleanMap f s = F s := by
  classical
  let f : PrebananaAtomEmbedding A B := {
    part := part
    fibre_nonempty := by
      intro a
      obtain ⟨b, hb⟩ := hsurj a
      exact ⟨b, by simp [prebananaFiber, hb]⟩
    fibre_mark_parity := by
      intro a
      exact prebanana_fibre_mark_parity_of_booleanMap F part hmap hparity a
  }
  refine ⟨f, ?_⟩
  intro s
  exact (hmap s).symm

end SuccessorTree.NonPrecompact
