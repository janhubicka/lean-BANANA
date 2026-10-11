import BANANA.NonPrecompact.PrebananaGridMarkedEmbeddings

/-!
# Finite strong amalgamation in pre-BANANA atom coordinates

The finite compatible-pair grid has even total marking and the two
projections are pre-BANANA atom embeddings, by the preceding modules.

The projections commute over the given common source. Exact
intersection of the two embedded Boolean algebras is the existing
fibre-product strong-intersection theorem, now transported through
the indexed grid equivalence.
-/

namespace SuccessorTree.NonPrecompact

/-- Both marked atom embeddings yield the same base partition map. -/
theorem prebananaGridMarkedEmbeddings_commute
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (i : Fin (prebananaGridMarkedStructure f g).atomCount) :
    f.part ((prebananaGridLeftEmbedding f g).part i) =
      g.part ((prebananaGridRightEmbedding f g).part i) :=
  prebananaGridPart_commute f g i

/-- If a Boolean element of the finite grid is represented both
by a union of rows and by a union of columns, these unions are
pulled back from one element of the common base Boolean algebra. -/
theorem prebananaGridMarkedEmbeddings_exact_intersection
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (SB : Set (Fin B.atomCount))
    (SC : Set (Fin C.atomCount))
    (hcompat :
      ∀ i : Fin (prebananaGridMarkedStructure f g).atomCount,
        (prebananaGridLeftEmbedding f g).part i ∈ SB ↔
          (prebananaGridRightEmbedding f g).part i ∈ SC) :
    ∃ SA : Set (Fin A.atomCount),
      (∀ b, b ∈ SB ↔ f.part b ∈ SA) ∧
      (∀ c, c ∈ SC ↔ g.part c ∈ SA) := by
  classical
  apply exists_common_subset_of_fiberGrid
    f.part g.part f.part_surjective g.part_surjective SB SC
  intro p
  let e : FiberGrid f.part g.part ≃
      Fin (prebananaGridMarkedStructure f g).atomCount :=
    Fintype.equivFin (FiberGrid f.part g.part)
  have hp := hcompat (e p)
  change (e.symm (e p)).2.1.1 ∈ SB ↔
    (e.symm (e p)).2.2.1 ∈ SC at hp
  rw [e.symm_apply_apply] at hp
  exact hp

/-- Strong amalgamation of finite pre-BANANA atom structures.

The finite amalgam has marked embeddings of B and C that commute
over A. Their image intersection, tested on all Boolean elements
(subsets of atoms), is exactly the common image of A. -/
theorem exists_prebananaAtomStrongAmalgam
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C) :
    ∃ D : PrebananaAtomStructure,
      ∃ u : PrebananaAtomEmbedding B D,
        ∃ v : PrebananaAtomEmbedding C D,
          (∀ i : Fin D.atomCount,
            f.part (u.part i) = g.part (v.part i)) ∧
          (∀ (SB : Set (Fin B.atomCount))
             (SC : Set (Fin C.atomCount)),
            (∀ i : Fin D.atomCount,
              u.part i ∈ SB ↔ v.part i ∈ SC) →
            ∃ SA : Set (Fin A.atomCount),
              (∀ b, b ∈ SB ↔ f.part b ∈ SA) ∧
              (∀ c, c ∈ SC ↔ g.part c ∈ SA)) := by
  refine ⟨prebananaGridMarkedStructure f g,
    prebananaGridLeftEmbedding f g,
    prebananaGridRightEmbedding f g, ?_, ?_⟩
  · intro i
    exact prebananaGridMarkedEmbeddings_commute f g i
  · intro SB SC hcompat
    exact prebananaGridMarkedEmbeddings_exact_intersection f g SB SC hcompat

end SuccessorTree.NonPrecompact
