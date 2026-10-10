import BANANA.NonPrecompact.PrebananaAmalgamBridge
import BANANA.NonPrecompact.FiberProductParityAmalgam

/-!
# Enumerating the compatible atom grid as an ordinary finite atom set

The pre-BANANA finite-atom API uses indices Fin n, whereas the
canonical strong amalgamation diagram has an atom for each compatible
pair (b,c) over a common source atom. This file constructs a
finite enumeration of the compatible grid and transports its two
surjective projections.

The exact intersection lemma is expressed at the level of subsets of
the old atom sets, matching the Boolean-subalgebra statement: if the
inverse images of a subset of B and a subset of C in the grid agree,
both subsets come from one subset of A.

These results are purely finite set theory. The parity marking of
the reindexed amalgam is packaged in a subsequent module.
-/

namespace SuccessorTree.NonPrecompact

/-- The atom grid of any two embeddings into pre-BANANA has at least
one element, even when the only source atom is unmarked. -/
theorem prebananaFiberGrid_nonempty
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    Nonempty (FiberGrid f.part g.part) := by
  let b := B.zeroAtom
  obtain ⟨c, hc⟩ := g.part_surjective (f.part b)
  exact ⟨⟨f.part b, (⟨b, rfl⟩, ⟨c, hc⟩)⟩⟩

/-- The total number of compatible grid atoms is positive. -/
theorem prebananaFiberGrid_card_pos
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    0 < Fintype.card (FiberGrid f.part g.part) := by
  classical
  exact Fintype.card_pos_iff.mpr (prebananaFiberGrid_nonempty f g)

/-- A finite enumeration of the compatible grid. This makes it
possible to use the standard Fin-indexed pre-BANANA structures. -/
noncomputable def prebananaGridIndexEquiv
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    Fin (Fintype.card (FiberGrid f.part g.part)) ≃
      FiberGrid f.part g.part := by
  classical
  exact (Fintype.equivFin (FiberGrid f.part g.part)).symm

/-- The B atom below a chosen amalgam grid atom. -/
noncomputable def prebananaGridPartB
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    Fin (Fintype.card (FiberGrid f.part g.part)) →
      Fin B.atomCount :=
  fun i => ((prebananaGridIndexEquiv f g) i).2.1.1

/-- The C atom below a chosen amalgam grid atom. -/
noncomputable def prebananaGridPartC
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    Fin (Fintype.card (FiberGrid f.part g.part)) →
      Fin C.atomCount :=
  fun i => ((prebananaGridIndexEquiv f g) i).2.2.1

theorem prebananaGridPartB_surjective
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    Function.Surjective (prebananaGridPartB f g) := by
  intro b
  obtain ⟨c, hc⟩ := g.part_surjective (f.part b)
  let p : FiberGrid f.part g.part :=
    ⟨f.part b, (⟨b, rfl⟩, ⟨c, hc⟩)⟩
  refine ⟨(prebananaGridIndexEquiv f g).symm p, ?_⟩
  change (((prebananaGridIndexEquiv f g)
    ((prebananaGridIndexEquiv f g).symm p)).2.1.1) = b
  rw [Equiv.apply_symm_apply]

theorem prebananaGridPartC_surjective
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    Function.Surjective (prebananaGridPartC f g) := by
  intro c
  obtain ⟨b, hb⟩ := f.part_surjective (g.part c)
  let p : FiberGrid f.part g.part :=
    ⟨g.part c, (⟨b, hb⟩, ⟨c, rfl⟩)⟩
  refine ⟨(prebananaGridIndexEquiv f g).symm p, ?_⟩
  change (((prebananaGridIndexEquiv f g)
    ((prebananaGridIndexEquiv f g).symm p)).2.2.1) = c
  rw [Equiv.apply_symm_apply]

/-- The two Boolean subalgebras of the compatible grid have exactly
the common A-image as intersection. This statement works even for
subsets of atoms with no parity constraint. -/
theorem prebananaGrid_exact_common_subsets
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (SB : Set (Fin B.atomCount))
    (SC : Set (Fin C.atomCount))
    (h :
      ∀ i : Fin (Fintype.card (FiberGrid f.part g.part)),
        prebananaGridPartB f g i ∈ SB ↔
          prebananaGridPartC f g i ∈ SC) :
    ∃ SA : Set (Fin A.atomCount),
      (∀ b, b ∈ SB ↔ f.part b ∈ SA) ∧
      (∀ c, c ∈ SC ↔ g.part c ∈ SA) := by
  apply exists_common_subset_of_fiberGrid
    f.part g.part f.part_surjective g.part_surjective SB SC
  intro p
  have hp := h ((prebananaGridIndexEquiv f g).symm p)
  change
    (((prebananaGridIndexEquiv f g)
      ((prebananaGridIndexEquiv f g).symm p)).2.1.1 ∈ SB ↔
      ((prebananaGridIndexEquiv f g)
      ((prebananaGridIndexEquiv f g).symm p)).2.2.1 ∈ SC) at hp
  rw [Equiv.apply_symm_apply] at hp
  exact hp

end SuccessorTree.NonPrecompact
