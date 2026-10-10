import BANANA.NonPrecompact.PrebananaAmalgamBridge
import BANANA.NonPrecompact.FiberProductParityAmalgam

/-!
# Compatible marginals of the pre-BANANA atom-grid amalgam

A pre-BANANA embedding in atom coordinates is a surjection from
target atoms to source atoms with the correct parity sum in
every fibre. Given A→B and A→C, the two collections of marks
have the same total on every fibre over each source atom.
This supplies the hypothesis needed for the column-sum lemma
of the star-matrix grid construction.

The two projections from the compatible atom grid to B and C
are both surjective. Together with the already verified
strong-intersection lemma, these establish the combinatorial
shape of the intended Boolean-algebra amalgam.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- Reindex the mark sum of a finite source fibre from a filtered
Finset to the subtype representing the same fibre. -/
theorem PrebananaAtomEmbedding.sum_mark_leftFiber
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (a : Fin A.atomCount) :
    (∑ b : LeftFiber f.part a, B.mark b.1) = A.mark a := by
  classical
  simpa [LeftFiber, prebananaFiber, Fintype.sum_subtype] using
    f.sum_mark_fibre a

/-- If two finite atom embeddings have the same source, the total
marks on the two fibres above any source atom coincide. -/
theorem prebanana_common_fiber_mark_totals
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (a : Fin A.atomCount) :
    (∑ b : LeftFiber f.part a, B.mark b.1) =
      ∑ c : RightFiber g.part a, C.mark c.1 := by
  calc
    (∑ b : LeftFiber f.part a, B.mark b.1) =
      A.mark a := f.sum_mark_leftFiber a
    _ = ∑ c : RightFiber g.part a, C.mark c.1 :=
      (g.sum_mark_leftFiber a).symm

/-- Projection of a compatible grid atom to its B atom. -/
def prebananaGridToB
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    FiberGrid f.part g.part → Fin B.atomCount :=
  fun p => p.2.1.1

/-- Projection of a compatible grid atom to its C atom. -/
def prebananaGridToC
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    FiberGrid f.part g.part → Fin C.atomCount :=
  fun p => p.2.2.1

theorem prebananaGridToB_surjective
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    Function.Surjective (prebananaGridToB f g) := by
  intro b
  obtain ⟨c, hc⟩ := g.part_surjective (f.part b)
  refine ⟨⟨f.part b, (⟨b, rfl⟩, ⟨c, hc⟩)⟩, rfl⟩

theorem prebananaGridToC_surjective
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    Function.Surjective (prebananaGridToC f g) := by
  intro c
  obtain ⟨b, hb⟩ := f.part_surjective (g.part c)
  refine ⟨⟨g.part c, (⟨b, hb⟩, ⟨c, rfl⟩)⟩, rfl⟩

end SuccessorTree.NonPrecompact
