import BANANA.NonPrecompact.PrebananaGridStrongAmalgam

/-!
# Boolean elements from marked finite atoms

An element of a finite Boolean algebra is the set of its atoms.
In the standard finite atom presentation, elements are therefore
finite subsets of `Fin A.atomCount`. The additive F₂ marking
is the marked-atom count modulo two. A partition map on atoms
acts on Boolean elements by inverse image.

This file proves the actual Boolean operations and marking
identities for this powerset presentation. Extending the result
to the abstract finite Boolean-algebra representation theorem is
a separate interface obligation.
-/

namespace SuccessorTree.NonPrecompact

/-- The parity predicate on a Boolean element represented as a
subset of the finite atom set. -/
def prebananaBooleanParity
    (A : PrebananaAtomStructure)
    (s : Finset (Fin A.atomCount)) : F2 :=
  (prebananaMarkedCount A.mark s : F2)

/-- A partition map on atoms induces a map of Boolean elements:
the image of a subset is the union of its target-atom fibres. -/
def prebananaBooleanMap
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (s : Finset (Fin A.atomCount)) :
    Finset (Fin B.atomCount) :=
  Finset.univ.filter fun b => f.part b ∈ s

theorem prebananaBooleanParity_empty
    (A : PrebananaAtomStructure) :
    prebananaBooleanParity A ∅ = 0 := by
  simp [prebananaBooleanParity, prebananaMarkedCount]

theorem prebananaBooleanParity_univ
    (A : PrebananaAtomStructure) :
    prebananaBooleanParity A Finset.univ = 0 :=
  A.total_mark_parity

theorem prebananaBooleanParity_union_disjoint
    (A : PrebananaAtomStructure)
    (s t : Finset (Fin A.atomCount))
    (h : Disjoint s t) :
    prebananaBooleanParity A (s ∪ t) =
      prebananaBooleanParity A s +
      prebananaBooleanParity A t := by
  simp only [prebananaBooleanParity, prebananaMarkedCount_cast_eq_sum]
  exact Finset.sum_union h

theorem prebananaBooleanMap_empty
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B) :
    prebananaBooleanMap f ∅ = ∅ := by
  classical
  ext b
  simp [prebananaBooleanMap]

theorem prebananaBooleanMap_univ
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B) :
    prebananaBooleanMap f Finset.univ = Finset.univ := by
  classical
  ext b
  simp [prebananaBooleanMap]

theorem prebananaBooleanMap_union
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (s t : Finset (Fin A.atomCount)) :
    prebananaBooleanMap f (s ∪ t) =
      prebananaBooleanMap f s ∪ prebananaBooleanMap f t := by
  classical
  ext b
  simp [prebananaBooleanMap]

theorem prebananaBooleanMap_inter
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (s t : Finset (Fin A.atomCount)) :
    prebananaBooleanMap f (s ∩ t) =
      prebananaBooleanMap f s ∩ prebananaBooleanMap f t := by
  classical
  ext b
  simp [prebananaBooleanMap]

theorem prebananaBooleanMap_complement
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (s : Finset (Fin A.atomCount)) :
    prebananaBooleanMap f (Finset.univ \ s) =
      Finset.univ \ prebananaBooleanMap f s := by
  classical
  ext b
  simp [prebananaBooleanMap]

theorem prebananaBooleanMap_injective
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B) :
    Function.Injective (prebananaBooleanMap f) := by
  classical
  intro s t h
  ext a
  obtain ⟨b, hb⟩ := f.part_surjective a
  have heq := congrArg
    (fun u : Finset (Fin B.atomCount) => b ∈ u) h
  simpa [prebananaBooleanMap, hb] using heq

/-- The marking is preserved on *every Boolean element*, not
only on the atoms of the source. This uses the already proved
partition-of-marked-count identity. -/
theorem prebananaBooleanMap_parity
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (s : Finset (Fin A.atomCount)) :
    prebananaBooleanParity B (prebananaBooleanMap f s) =
      prebananaBooleanParity A s := by
  classical
  change
    (prebananaMarkedCount B.mark
      (Finset.univ.filter fun b => f.part b ∈ s) : F2) =
    (prebananaMarkedCount A.mark s : F2)
  calc
    (prebananaMarkedCount B.mark
      (Finset.univ.filter fun b => f.part b ∈ s) : F2) =
        ((∑ a ∈ s,
          prebananaMarkedCount B.mark
            (prebananaFiber f.part a)) : F2) := by
        exact congrArg (fun n : ℕ => (n : F2))
          (prebanana_sum_fiber_markedCount B.mark f.part s).symm
    _ = ∑ a ∈ s,
          (prebananaMarkedCount B.mark
            (prebananaFiber f.part a) : F2) := by
        simp only [Nat.cast_sum]
    _ = ∑ a ∈ s, A.mark a := by
        apply Finset.sum_congr rfl
        intro a ha
        exact f.fibre_mark_parity a
    _ = (prebananaMarkedCount A.mark s : F2) :=
        (prebananaMarkedCount_cast_eq_sum A.mark s).symm

end SuccessorTree.NonPrecompact
