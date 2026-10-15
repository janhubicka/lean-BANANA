import BANANA.NonPrecompact.PrebananaUniformSuffixSelection

/-!
# Distinct marked suffix witnesses for arbitrary finite target atom sets

Any finite target atom type β can be numbered by Fin (Fintype.card β).
Use this numbering to give each target atom one length-k suffix,
with exactly one reset letter 0 or 2 and all other letters 4.
The suffixes are pairwise distinct and carry the prescribed F₂
mark, regardless of the mark of the parent atom.

This removes the Fin-indexing convention from the witness-selection
lemma. The base-fibre dependence and the complete extension diagram
are still to be proved.
-/

namespace SuccessorTree.NonPrecompact

/-- One marked length-card(β) descendant for each target atom b : β. -/
noncomputable def prebananaTargetSuffix
    (β : Type*) [Fintype β] (mark : β → F2) (b : β) :
    PrebananaFiveAryWord (Fintype.card β) := by
  classical
  let e : β ≃ Fin (Fintype.card β) := Fintype.equivFin β
  exact prebananaSelectedSuffix (Fintype.card β)
    (fun i => mark (e.symm i)) (e b)

/-- Every target witness has exactly its prescribed mark below
an arbitrary parent marked p. -/
theorem prebananaTargetSuffix_mark
    (β : Type*) [Fintype β]
    (mark : β → F2) (p : F2) (b : β) :
    prebananaFiveAryDescendantMark p (Fintype.card β)
      (prebananaTargetSuffix β mark b) = mark b := by
  classical
  unfold prebananaTargetSuffix
  simp only [prebananaSelectedSuffix_mark, Equiv.symm_apply_apply]

/-- Witness suffixes indexed by an arbitrary finite target type
are injective, even when different atoms prescribe different marks. -/
theorem prebananaTargetSuffix_injective
    (β : Type*) [Fintype β] (mark : β → F2) :
    Function.Injective (prebananaTargetSuffix β mark) := by
  classical
  let e : β ≃ Fin (Fintype.card β) := Fintype.equivFin β
  intro b c h
  have hinj := prebananaSelectedSuffix_injective
    (Fintype.card β) (fun i => mark (e.symm i))
  have he : e b = e c := hinj h
  exact e.injective he

end SuccessorTree.NonPrecompact
