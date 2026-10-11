import BANANA.NonPrecompact.PrebananaAbstractAtomCodes
import BANANA.NonPrecompact.PrebananaAbstractAtomsLiteral
import BANANA.NonPrecompact.PrebananaPowersetBridge

/-!
# Boolean elements of abstract finite pre-BANANA objects in atom codes

For a finite Boolean algebra, represent each element by the `Fin`
indices of the abstract atoms beneath it. The parity of the
corresponding element in the concrete marked atom code is exactly
the original additive parity value.

This is the element-level parity preservation needed to transport
the concrete powerset strong-amalgamation theorem back to
arbitrary finite Boolean structures.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- Encode an abstract finite Boolean element as the finite subset
of enumerated atom indices below it. -/
noncomputable def prebananaAbstractBooleanCode
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (x : α) :
    Finset (Fin (Fintype.card (PrebananaAbstractAtoms α))) := by
  classical
  exact
    ((prebananaFiniteBooleanAtomFinsetOrderIso α) x).image
      (prebananaAbstractAtomIndex α).symm

/-- Evaluating the marked finite atom code at the represented
Boolean element recovers the original abstract parity. -/
theorem prebananaAbstractBooleanCode_parity
    (α : Type*) [BooleanAlgebra α] [Fintype α] [Nontrivial α]
    (μ : α → F2)
    (hzero : μ ⊥ = 0)
    (htop : μ ⊤ = 0)
    (hadd : ∀ x y : α, x ⊓ y = ⊥ →
      μ (x ⊔ y) = μ x + μ y)
    (x : α) :
    prebananaBooleanParity
      (prebananaAbstractAtomCode α μ hzero htop hadd)
      (prebananaAbstractBooleanCode α x) = μ x := by
  classical
  let e := prebananaAbstractAtomIndex α
  let S := (prebananaFiniteBooleanAtomFinsetOrderIso α) x
  let A := prebananaAbstractAtomCode α μ hzero htop hadd
  have hmark (a : PrebananaAbstractAtoms α) :
      A.mark (e.symm a) = μ (a : α) := by
    change μ ((prebananaFiniteBooleanAtomFinsetOrderIso α).symm
      ({e (e.symm a)} : Finset (PrebananaAbstractAtoms α))) = μ (a : α)
    rw [e.apply_symm_apply]
    exact congrArg μ
      (prebananaFiniteBoolean_singleton_represents_atom α a)
  change (prebananaMarkedCount A.mark (S.image e.symm) : F2) = μ x
  rw [prebananaMarkedCount_cast_eq_sum]
  calc
    (∑ i ∈ S.image e.symm, A.mark i) =
      ∑ a ∈ S, A.mark (e.symm a) := by
        exact Finset.sum_image e.symm.injective.injOn
    _ = ∑ a ∈ S, μ (a : α) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hmark a
    _ = μ x := by
      exact (prebananaAbstractParity_atomSum_on_atoms α μ hzero hadd x).symm

end SuccessorTree.NonPrecompact
