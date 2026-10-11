import BANANA.NonPrecompact.PrebananaFiniteBooleanRepresentation

/-!
# Finitely additive markings on arbitrary finite Boolean algebras

The circulation definition of pre-BANANA starts with a function
`mu : α → F2` additive on disjoint joins, not with atom markings.

This module proves that such a function is uniquely determined by
its values on the singleton atoms of the finite Boolean-powerset
representation. In particular, `mu top = 0` implies an even
total atom marking.

This is the parity part of the abstract-to-atom presentation bridge.
Translation of arbitrary embeddings is still separate.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators Classical

/-- A finitely additive F₂-valued function on finite subsets is
determined by its singleton values. -/
theorem prebanana_disjointAdditiveFinset_sum
    {ι : Type*} [DecidableEq ι]
    (ν : Finset ι → F2)
    (hzero : ν ∅ = 0)
    (hadd : ∀ s t : Finset ι, Disjoint s t →
      ν (s ∪ t) = ν s + ν t)
    (s : Finset ι) :
    ν s = ∑ i ∈ s, ν {i} := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using hzero
  | @insert a s ha ih =>
      have hd : Disjoint ({a} : Finset ι) s := by
        simpa using ha
      calc
        ν (insert a s) = ν ({a} ∪ s) := by
          rw [Finset.singleton_union]
        _ = ν {a} + ν s := hadd _ _ hd
        _ = ν {a} + ∑ i ∈ s, ν {i} := by rw [ih]
        _ = ∑ i ∈ insert a s, ν {i} := by
          rw [Finset.sum_insert ha]

/-- A parity function on a finite Boolean algebra is the sum
of its values on the singleton atoms in the canonical powerset
representation. -/
theorem prebananaAbstractParity_atomSum
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (μ : α → F2)
    (hzero : μ ⊥ = 0)
    (hadd : ∀ x y : α, x ⊓ y = ⊥ →
      μ (x ⊔ y) = μ x + μ y)
    (x : α) :
    μ x =
      ∑ a ∈ prebananaFiniteBooleanAtomFinsetOrderIso α x,
        μ ((prebananaFiniteBooleanAtomFinsetOrderIso α).symm
          ({a} : Finset (PrebananaAbstractAtoms α))) := by
  classical
  let e := prebananaFiniteBooleanAtomFinsetOrderIso α
  let ν : Finset (PrebananaAbstractAtoms α) → F2 :=
    fun s => μ (e.symm s)
  have he_bot : e.symm (∅ : Finset (PrebananaAbstractAtoms α)) =
      (⊥ : α) := e.symm.map_bot
  have hνzero : ν ∅ = 0 := by
    dsimp [ν]
    rw [he_bot]
    exact hzero
  have hνadd (s t : Finset (PrebananaAbstractAtoms α))
      (hd : Disjoint s t) :
      ν (s ∪ t) = ν s + ν t := by
    have hsup : e.symm (s ∪ t) = e.symm s ⊔ e.symm t := by
      change e.symm (s ⊔ t) = e.symm s ⊔ e.symm t
      exact e.symm.map_sup s t
    have hinf : e.symm s ⊓ e.symm t = (⊥ : α) := by
      calc
        e.symm s ⊓ e.symm t = e.symm (s ∩ t) := by
          change e.symm s ⊓ e.symm t = e.symm (s ⊓ t)
          exact (e.symm.map_inf s t).symm
        _ = e.symm (∅ : Finset (PrebananaAbstractAtoms α)) := by
          rw [Finset.disjoint_iff_inter_eq_empty.mp hd]
        _ = ⊥ := e.symm.map_bot
    change μ (e.symm (s ∪ t)) =
      μ (e.symm s) + μ (e.symm t)
    rw [hsup]
    exact hadd (e.symm s) (e.symm t) hinf
  have hsum :=
    prebanana_disjointAdditiveFinset_sum ν hνzero hνadd (e x)
  change μ (e.symm (e x)) =
    ∑ a ∈ e x, μ (e.symm ({a} : Finset (PrebananaAbstractAtoms α))) at hsum
  rw [e.symm_apply_apply] at hsum
  exact hsum

/-- If the parity function vanishes at top, the sum of the
single-atom parities in its finite representation is zero. -/
theorem prebananaAbstractParity_total_even
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (μ : α → F2)
    (hzero : μ ⊥ = 0)
    (htop : μ ⊤ = 0)
    (hadd : ∀ x y : α, x ⊓ y = ⊥ →
      μ (x ⊔ y) = μ x + μ y) :
    (∑ a : PrebananaAbstractAtoms α,
      μ ((prebananaFiniteBooleanAtomFinsetOrderIso α).symm
        ({a} : Finset (PrebananaAbstractAtoms α)))) = 0 := by
  classical
  let e := prebananaFiniteBooleanAtomFinsetOrderIso α
  have hsum := prebananaAbstractParity_atomSum α μ hzero hadd (⊤ : α)
  have he_top : e (⊤ : α) = Finset.univ := e.map_top
  change μ (⊤ : α) =
    ∑ a ∈ e (⊤ : α),
      μ (e.symm ({a} : Finset (PrebananaAbstractAtoms α))) at hsum
  rw [htop, he_top] at hsum
  simpa using hsum.symm

end SuccessorTree.NonPrecompact
