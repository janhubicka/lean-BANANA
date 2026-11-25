import BANANA.NonPrecompact.PrebananaGridProjections
import BANANA.NonPrecompact.FiberGridFibreEquivs

/-!
# Exact fibres of the finite compatible-atom grid

The left fibre of a grid projection above a B atom is canonically
equivalent to its compatible C fibre. The analogous statement holds
for the right projection. These equivalences will transport the
already proved star-matrix row and column parity identities to the
finite atom-coordinate presentation, without assuming any extra
parity axioms.
-/

namespace SuccessorTree.NonPrecompact

/-- The indexed finite left fibre is equivalent to the corresponding
unindexed grid fibre. -/
noncomputable def prebananaGridLeftIndexFiberEquiv
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (b : Fin B.atomCount) :
    {i : Fin (prebananaGridMarkedStructure f g).atomCount //
      prebananaGridLeftPart f g i = b} ≃
    {p : FiberGrid f.part g.part // p.2.1.1 = b} := by
  classical
  let e : Fin (prebananaGridMarkedStructure f g).atomCount ≃
      FiberGrid f.part g.part :=
    (Fintype.equivFin (FiberGrid f.part g.part)).symm
  refine {
    toFun := fun i => ⟨e i.1, ?_⟩
    invFun := fun p => ⟨e.symm p.1, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · exact i.2
  · change (e (e.symm p.1)).2.1.1 = b
    rw [e.apply_symm_apply]
    exact p.2
  · intro i
    apply Subtype.ext
    exact e.symm_apply_apply i.1
  · intro p
    apply Subtype.ext
    exact e.apply_symm_apply p.1

/-- The corresponding indexed finite right fibre equivalence. -/
noncomputable def prebananaGridRightIndexFiberEquiv
    {A B C : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    (g : PrebananaAtomEmbedding A C)
    (c : Fin C.atomCount) :
    {i : Fin (prebananaGridMarkedStructure f g).atomCount //
      prebananaGridRightPart f g i = c} ≃
    {p : FiberGrid f.part g.part // p.2.2.1 = c} := by
  classical
  let e : Fin (prebananaGridMarkedStructure f g).atomCount ≃
      FiberGrid f.part g.part :=
    (Fintype.equivFin (FiberGrid f.part g.part)).symm
  refine {
    toFun := fun i => ⟨e i.1, ?_⟩
    invFun := fun p => ⟨e.symm p.1, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · exact i.2
  · change (e (e.symm p.1)).2.2.1 = c
    rw [e.apply_symm_apply]
    exact p.2
  · intro i
    apply Subtype.ext
    exact e.symm_apply_apply i.1
  · intro p
    apply Subtype.ext
    exact e.apply_symm_apply p.1

end SuccessorTree.NonPrecompact
