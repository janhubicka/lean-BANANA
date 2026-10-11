import BANANA.NonPrecompact.PrebananaAbstractParityDecomposition

/-!
# Coding arbitrary nontrivial finite Boolean parity structures by Fin-atoms

The circulation class consists of nontrivial finite Boolean algebras
carrying disjoint-additive F₂ markings. An abstract finite Boolean
algebra has a nonempty finite set of atoms. Enumerating these atoms by
`Fin` and using the singleton representatives from the canonical
powerset order isomorphism gives an actual `PrebananaAtomStructure`.

The total marking is zero by the already verified parity-decomposition
lemma, so the code satisfies every pre-BANANA atom-structure axiom.
Translation of arbitrary *embeddings* is a separate task.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- Every nontrivial finite Boolean algebra has an atom. -/
theorem prebananaAbstractAtoms_nonempty
    (α : Type*) [BooleanAlgebra α] [Fintype α] [Nontrivial α] :
    Nonempty (PrebananaAbstractAtoms α) := by
  classical
  letI : CompleteAtomicBooleanAlgebra α :=
    Fintype.toCompleteAtomicBooleanAlgebra α
  obtain ⟨a, ha⟩ := (IsAtomic.exists_atom (α := α))
  exact ⟨⟨a, ha⟩⟩

/-- Its finite atom count is positive. -/
theorem prebananaAbstractAtoms_card_pos
    (α : Type*) [BooleanAlgebra α] [Fintype α] [Nontrivial α] :
    0 < Fintype.card (PrebananaAbstractAtoms α) := by
  classical
  exact Fintype.card_pos_iff.mpr (prebananaAbstractAtoms_nonempty α)

/-- Canonical finite enumeration of the abstract atoms. -/
noncomputable def prebananaAbstractAtomIndex
    (α : Type*) [BooleanAlgebra α] [Fintype α] :
    Fin (Fintype.card (PrebananaAbstractAtoms α)) ≃
      PrebananaAbstractAtoms α := by
  classical
  exact (Fintype.equivFin (PrebananaAbstractAtoms α)).symm

/-- Every abstract nontrivial finite Boolean parity structure has a
concrete Fin-indexed marked atom presentation. -/
noncomputable def prebananaAbstractAtomCode
    (α : Type*) [BooleanAlgebra α] [Fintype α] [Nontrivial α]
    (μ : α → F2)
    (hzero : μ ⊥ = 0)
    (htop : μ ⊤ = 0)
    (hadd : ∀ x y : α, x ⊓ y = ⊥ →
      μ (x ⊔ y) = μ x + μ y) :
    PrebananaAtomStructure where
  atomCount := Fintype.card (PrebananaAbstractAtoms α)
  atomCount_pos := prebananaAbstractAtoms_card_pos α
  mark := fun i =>
    μ ((prebananaFiniteBooleanAtomFinsetOrderIso α).symm
      ({prebananaAbstractAtomIndex α i} :
        Finset (PrebananaAbstractAtoms α)))
  total_mark_parity := by
    classical
    rw [prebananaMarkedCount_cast_eq_sum]
    let e := prebananaAbstractAtomIndex α
    change (∑ i : Fin (Fintype.card (PrebananaAbstractAtoms α)),
      μ ((prebananaFiniteBooleanAtomFinsetOrderIso α).symm
        ({e i} : Finset (PrebananaAbstractAtoms α)))) = 0
    calc
      (∑ i : Fin (Fintype.card (PrebananaAbstractAtoms α)),
        μ ((prebananaFiniteBooleanAtomFinsetOrderIso α).symm
          ({e i} : Finset (PrebananaAbstractAtoms α)))) =
      ∑ a : PrebananaAbstractAtoms α,
        μ ((prebananaFiniteBooleanAtomFinsetOrderIso α).symm
          ({a} : Finset (PrebananaAbstractAtoms α))) :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = 0 := prebananaAbstractParity_total_even α μ hzero htop hadd

end SuccessorTree.NonPrecompact
