import BANANA.NonPrecompact.PrebananaPowersetBridge

/-!
# Strong amalgamation on finite Boolean elements

The atom-grid strong-amalgamation theorem is transported to
actual Boolean elements, represented as arbitrary subsets of
the finite atom set. Both common-image commutativity and exact
intersection now hold for elements, not only for atom maps.

The remaining external representation step is to identify an
arbitrary finite Boolean algebra with the powerset of its atoms.
-/

namespace SuccessorTree.NonPrecompact

/-- The two embeddings of the finite grid agree on *every*
element of the common source Boolean algebra. -/
theorem prebananaBooleanGrid_commute
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (s : Finset (Fin A.atomCount)) :
    prebananaBooleanMap (prebananaGridLeftEmbedding f g)
      (prebananaBooleanMap f s) =
    prebananaBooleanMap (prebananaGridRightEmbedding f g)
      (prebananaBooleanMap g s) := by
  classical
  ext i
  simp only [prebananaBooleanMap, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [prebananaGridMarkedEmbeddings_commute f g i]

/-- If the image of a B-element equals that of a C-element,
both elements come from one A-element. The common element is
explicitly a finite set of base atoms. -/
theorem prebananaBooleanGrid_exact_intersection
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (s : Finset (Fin B.atomCount))
    (t : Finset (Fin C.atomCount))
    (h :
      prebananaBooleanMap (prebananaGridLeftEmbedding f g) s =
      prebananaBooleanMap (prebananaGridRightEmbedding f g) t) :
    ∃ r : Finset (Fin A.atomCount),
      prebananaBooleanMap f r = s ∧
      prebananaBooleanMap g r = t := by
  classical
  have hcompat (i : Fin (prebananaGridMarkedStructure f g).atomCount) :
      (prebananaGridLeftEmbedding f g).part i ∈ s ↔
      (prebananaGridRightEmbedding f g).part i ∈ t := by
    have hi :
        i ∈ prebananaBooleanMap (prebananaGridLeftEmbedding f g) s ↔
        i ∈ prebananaBooleanMap (prebananaGridRightEmbedding f g) t := by
      rw [h]
    simpa [prebananaBooleanMap] using hi
  obtain ⟨SA, hB, hC⟩ :=
    prebananaGridMarkedEmbeddings_exact_intersection f g
      (s : Set (Fin B.atomCount)) (t : Set (Fin C.atomCount)) hcompat
  let r : Finset (Fin A.atomCount) :=
    Finset.univ.filter fun a => a ∈ SA
  refine ⟨r, ?_, ?_⟩
  · ext b
    simpa [r, prebananaBooleanMap] using (hB b).symm
  · ext c
    simpa [r, prebananaBooleanMap] using (hC c).symm

/-- Finite strong amalgamation stated directly at the level
of all Boolean elements of the canonical powerset models. -/
theorem exists_prebananaPowersetStrongAmalgam
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    ∃ D : PrebananaAtomStructure,
      ∃ u : PrebananaAtomEmbedding B D,
        ∃ v : PrebananaAtomEmbedding C D,
          (∀ s : Finset (Fin A.atomCount),
            prebananaBooleanMap u (prebananaBooleanMap f s) =
            prebananaBooleanMap v (prebananaBooleanMap g s)) ∧
          (∀ (s : Finset (Fin B.atomCount))
             (t : Finset (Fin C.atomCount)),
            prebananaBooleanMap u s = prebananaBooleanMap v t →
            ∃ r : Finset (Fin A.atomCount),
              prebananaBooleanMap f r = s ∧
              prebananaBooleanMap g r = t) := by
  refine ⟨prebananaGridMarkedStructure f g,
    prebananaGridLeftEmbedding f g,
    prebananaGridRightEmbedding f g, ?_, ?_⟩
  · intro s
    exact prebananaBooleanGrid_commute f g s
  · intro s t h
    exact prebananaBooleanGrid_exact_intersection f g s t h

end SuccessorTree.NonPrecompact
