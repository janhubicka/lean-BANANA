import BANANA.NonPrecompact.PrebananaIndexedParity

/-!
# Coordinate projections of the indexed finite pre-BANANA grid

The parity-marked finite structure was constructed in
`PrebananaIndexedParity`. This module supplies its underlying
atom-partition maps and their surjectivity and compatibility.
The marked-fibre identities, which turn these maps into pre-BANANA
embeddings, remain a separate obligation.
-/

namespace SuccessorTree.NonPrecompact

/-- The projection from the reindexed compatible grid to B atoms. -/
noncomputable def prebananaGridLeftPart
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    Fin (prebananaGridMarkedStructure f g).atomCount →
      Fin B.atomCount :=
  fun i =>
    ((Fintype.equivFin (FiberGrid f.part g.part)).symm i).2.1.1

/-- The projection from the reindexed compatible grid to C atoms. -/
noncomputable def prebananaGridRightPart
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    Fin (prebananaGridMarkedStructure f g).atomCount →
      Fin C.atomCount :=
  fun i =>
    ((Fintype.equivFin (FiberGrid f.part g.part)).symm i).2.2.1

theorem prebananaGridLeftPart_surjective
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    Function.Surjective (prebananaGridLeftPart f g) := by
  classical
  intro b
  obtain ⟨c, hc⟩ := g.part_surjective (f.part b)
  let p : FiberGrid f.part g.part :=
    ⟨f.part b, (⟨b, rfl⟩, ⟨c, hc⟩)⟩
  refine ⟨(Fintype.equivFin (FiberGrid f.part g.part)) p, ?_⟩
  simp [prebananaGridLeftPart, p, prebananaGridMarkedStructure]

theorem prebananaGridRightPart_surjective
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    Function.Surjective (prebananaGridRightPart f g) := by
  classical
  intro c
  obtain ⟨b, hb⟩ := f.part_surjective (g.part c)
  let p : FiberGrid f.part g.part :=
    ⟨g.part c, (⟨b, hb⟩, ⟨c, rfl⟩)⟩
  refine ⟨(Fintype.equivFin (FiberGrid f.part g.part)) p, ?_⟩
  simp [prebananaGridRightPart, p, prebananaGridMarkedStructure]

/-- Both projections induce the same map to the common base atoms. -/
theorem prebananaGridPart_commute
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (i : Fin (prebananaGridMarkedStructure f g).atomCount) :
    f.part (prebananaGridLeftPart f g i) =
      g.part (prebananaGridRightPart f g i) := by
  classical
  let p := (Fintype.equivFin (FiberGrid f.part g.part)).symm i
  change f.part p.2.1.1 = g.part p.2.2.1
  exact p.2.1.2.trans p.2.2.2.symm


/-- Every B atom has a nonempty fibre in the grid atom partition. -/
theorem prebananaGridLeftPart_fibre_nonempty
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (b : Fin B.atomCount) :
    (prebananaFiber (prebananaGridLeftPart f g) b).Nonempty := by
  classical
  obtain ⟨i, hi⟩ := prebananaGridLeftPart_surjective f g b
  refine ⟨i, ?_⟩
  simp [prebananaFiber, hi]

/-- Every C atom has a nonempty fibre in the grid atom partition. -/
theorem prebananaGridRightPart_fibre_nonempty
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (c : Fin C.atomCount) :
    (prebananaFiber (prebananaGridRightPart f g) c).Nonempty := by
  classical
  obtain ⟨i, hi⟩ := prebananaGridRightPart_surjective f g c
  refine ⟨i, ?_⟩
  simp [prebananaFiber, hi]

end SuccessorTree.NonPrecompact
