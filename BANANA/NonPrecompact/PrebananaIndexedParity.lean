import BANANA.NonPrecompact.PrebananaGridTotal
import BANANA.NonPrecompact.PrebananaAmalgamBridge

/-!
# Parity of the reindexed pre-BANANA fibre grid

The atom presentation of the circulated pre-BANANA class uses
`Fin n` indices, whereas the fibre-product parity theorem uses
an arbitrary finite compatible-pair grid. Reindexing its atoms
does not change the total F₂ marking.

This module proves exactly the parity obligation for the
candidate finite amalgam. Constructing its two marked
partition embeddings and proving strong intersection are
separate obligations.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- Reindexing a finite marking by an equivalence preserves
the marked-atom count modulo two. -/
theorem prebananaMarkedCount_reindex_eq_sum
    {ι : Type*} [Fintype ι]
    (e : Fin (Fintype.card ι) ≃ ι) (mark : ι → F2) :
    (prebananaMarkedCount
      (fun i : Fin (Fintype.card ι) => mark (e i))
      Finset.univ : F2) =
      ∑ x : ι, mark x := by
  classical
  rw [prebananaMarkedCount_cast_eq_sum]
  simpa only [Finset.sum_univ] using
    (Fintype.sum_equiv e
      (fun i : Fin (Fintype.card ι) => mark (e i))
      mark (fun i => rfl))

/-- An indexed compatible fibre-product grid has even marking.
The row and column requirements are *not* asserted by this
theorem; only the finite target's total-parity axiom is proved. -/
theorem prebananaIndexedGrid_total_zero
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (e : Fin (Fintype.card (FiberGrid f.part g.part)) ≃
      FiberGrid f.part g.part) :
    (prebananaMarkedCount
      (fun i =>
        fiberGridMark f.part g.part
          f.part_surjective g.part_surjective
          B.mark C.mark (e i))
      Finset.univ : F2) = 0 := by
  classical
  have hB : (∑ b : Fin B.atomCount, B.mark b) = 0 := by
    have h := B.total_mark_parity
    rw [prebananaMarkedCount_cast_eq_sum] at h
    simpa using h
  calc
    (prebananaMarkedCount
      (fun i =>
        fiberGridMark f.part g.part
          f.part_surjective g.part_surjective
          B.mark C.mark (e i))
      Finset.univ : F2) =
      ∑ p : FiberGrid f.part g.part,
        fiberGridMark f.part g.part
          f.part_surjective g.part_surjective
          B.mark C.mark p := by
          exact prebananaMarkedCount_reindex_eq_sum e _
    _ = 0 :=
      fiberGridMark_total_zero
        f.part g.part
        f.part_surjective g.part_surjective
        B.mark C.mark hB

/-- The fully reindexed fibre product is a genuine finite pre-BANANA
atom structure. The two projection maps are not yet supplied with
proofs that their individual fibres have the prescribed parities. -/
noncomputable def prebananaGridMarkedStructure
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) : PrebananaAtomStructure where
  atomCount := Fintype.card (FiberGrid f.part g.part)
  atomCount_pos := by
    classical
    apply Fintype.card_pos_iff.mpr
    let b := B.zeroAtom
    obtain ⟨c, hc⟩ := g.part_surjective (f.part b)
    exact ⟨⟨f.part b, (⟨b, rfl⟩, ⟨c, hc⟩)⟩⟩
  mark := fun i =>
    fiberGridMark f.part g.part
      f.part_surjective g.part_surjective B.mark C.mark
      ((Fintype.equivFin (FiberGrid f.part g.part)).symm i)
  total_mark_parity := by
    classical
    exact prebananaIndexedGrid_total_zero f g
      ((Fintype.equivFin (FiberGrid f.part g.part)).symm)

end SuccessorTree.NonPrecompact
