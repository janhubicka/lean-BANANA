import BANANA.NonPrecompact.PrebananaGridFibreEquivs

/-!
# Mark-preserving projections of the finite pre-BANANA grid

The reindexed finite grid carries the explicit star marking. Its
projection fibres are indexed by compatible rows and columns of the
original grid, so the previously formalised parity identities
establish that both projections preserve the prescribed marks.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- The F₂ marking of an original embedding, summed over a subtype
rather than over a filtered finite set. -/
theorem PrebananaAtomEmbedding.sum_mark_subtype
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (a : Fin A.atomCount) :
    (∑ b : {b : Fin B.atomCount // f.part b = a}, B.mark b.1) =
      A.mark a := by
  classical
  calc
    (∑ b : {b : Fin B.atomCount // f.part b = a}, B.mark b.1) =
        ∑ b ∈ prebananaFiber f.part a, B.mark b := by
      symm
      exact Finset.sum_subtype
        (prebananaFiber f.part a)
        (by intro b; simp [prebananaFiber])
        B.mark
    _ = A.mark a := f.sum_mark_fibre a

/-- The prescribed grid row mark agrees with the sum over the
corresponding fibre of the indexed atom projection. -/
theorem prebananaGridLeftPart_sum_mark
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (b : Fin B.atomCount) :
    (∑ i ∈ prebananaFiber (prebananaGridLeftPart f g) b,
       (prebananaGridMarkedStructure f g).mark i) =
      B.mark b := by
  classical
  calc
    (∑ i ∈ prebananaFiber (prebananaGridLeftPart f g) b,
       (prebananaGridMarkedStructure f g).mark i) =
      ∑ i : {i : Fin (prebananaGridMarkedStructure f g).atomCount //
        prebananaGridLeftPart f g i = b},
        (prebananaGridMarkedStructure f g).mark i.1 := by
          exact Finset.sum_subtype
            (prebananaFiber (prebananaGridLeftPart f g) b)
            (by intro i; simp [prebananaFiber])
            (prebananaGridMarkedStructure f g).mark
    _ = ∑ p : {p : FiberGrid f.part g.part // p.2.1.1 = b},
        fiberGridMark f.part g.part
          f.part_surjective g.part_surjective B.mark C.mark p.1 := by
          exact Fintype.sum_equiv
            (prebananaGridLeftIndexFiberEquiv f g b)
            (fun i => (prebananaGridMarkedStructure f g).mark i.1)
            (fun p => fiberGridMark f.part g.part
              f.part_surjective g.part_surjective B.mark C.mark p.1)
            (by intro i; rfl)
    _ = ∑ c : RightFiber g.part (f.part b),
        fiberGridMark f.part g.part
          f.part_surjective g.part_surjective B.mark C.mark
          ⟨f.part b, (⟨b, rfl⟩, c)⟩ := by
          symm
          exact Fintype.sum_equiv
            (fiberGridRowSubtypeEquiv f.part g.part b)
            (fun c => fiberGridMark f.part g.part
              f.part_surjective g.part_surjective B.mark C.mark
              ⟨f.part b, (⟨b, rfl⟩, c)⟩)
            (fun p => fiberGridMark f.part g.part
              f.part_surjective g.part_surjective B.mark C.mark p.1)
            (by intro c; rfl)
    _ = B.mark b :=
        sum_fiberGridMark_right f.part g.part
          f.part_surjective g.part_surjective B.mark C.mark b

/-- The analogous column-fibre marking identity. -/
theorem prebananaGridRightPart_sum_mark
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (c : Fin C.atomCount) :
    (∑ i ∈ prebananaFiber (prebananaGridRightPart f g) c,
       (prebananaGridMarkedStructure f g).mark i) =
      C.mark c := by
  classical
  have htotal (a : Fin A.atomCount) :
      (∑ b : LeftFiber f.part a, B.mark b.1) =
        ∑ d : RightFiber g.part a, C.mark d.1 := by
    exact (f.sum_mark_subtype a).trans (g.sum_mark_subtype a).symm
  calc
    (∑ i ∈ prebananaFiber (prebananaGridRightPart f g) c,
       (prebananaGridMarkedStructure f g).mark i) =
      ∑ i : {i : Fin (prebananaGridMarkedStructure f g).atomCount //
        prebananaGridRightPart f g i = c},
        (prebananaGridMarkedStructure f g).mark i.1 := by
          exact Finset.sum_subtype
            (prebananaFiber (prebananaGridRightPart f g) c)
            (by intro i; simp [prebananaFiber])
            (prebananaGridMarkedStructure f g).mark
    _ = ∑ p : {p : FiberGrid f.part g.part // p.2.2.1 = c},
        fiberGridMark f.part g.part
          f.part_surjective g.part_surjective B.mark C.mark p.1 := by
          exact Fintype.sum_equiv
            (prebananaGridRightIndexFiberEquiv f g c)
            (fun i => (prebananaGridMarkedStructure f g).mark i.1)
            (fun p => fiberGridMark f.part g.part
              f.part_surjective g.part_surjective B.mark C.mark p.1)
            (by intro i; rfl)
    _ = ∑ b : LeftFiber f.part (g.part c),
        fiberGridMark f.part g.part
          f.part_surjective g.part_surjective B.mark C.mark
          ⟨g.part c, (b, ⟨c, rfl⟩)⟩ := by
          symm
          exact Fintype.sum_equiv
            (fiberGridColumnSubtypeEquiv f.part g.part c)
            (fun b => fiberGridMark f.part g.part
              f.part_surjective g.part_surjective B.mark C.mark
              ⟨g.part c, (b, ⟨c, rfl⟩)⟩)
            (fun p => fiberGridMark f.part g.part
              f.part_surjective g.part_surjective B.mark C.mark p.1)
            (by intro b; rfl)
    _ = C.mark c :=
        sum_fiberGridMark_left f.part g.part
          f.part_surjective g.part_surjective B.mark C.mark
          htotal c

/-- The B-side marked atom embedding into the finite amalgam. -/
noncomputable def prebananaGridLeftEmbedding
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    PrebananaAtomEmbedding B (prebananaGridMarkedStructure f g) where
  part := prebananaGridLeftPart f g
  fibre_nonempty := prebananaGridLeftPart_fibre_nonempty f g
  fibre_mark_parity := by
    intro b
    rw [prebananaMarkedCount_cast_eq_sum]
    exact prebananaGridLeftPart_sum_mark f g b

/-- The C-side marked atom embedding into the finite amalgam. -/
noncomputable def prebananaGridRightEmbedding
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    PrebananaAtomEmbedding C (prebananaGridMarkedStructure f g) where
  part := prebananaGridRightPart f g
  fibre_nonempty := prebananaGridRightPart_fibre_nonempty f g
  fibre_mark_parity := by
    intro c
    rw [prebananaMarkedCount_cast_eq_sum]
    exact prebananaGridRightPart_sum_mark f g c

end SuccessorTree.NonPrecompact
