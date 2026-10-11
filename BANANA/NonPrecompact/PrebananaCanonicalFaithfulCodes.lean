import BANANA.NonPrecompact.PrebananaCodedStrongAmalgam
import BANANA.NonPrecompact.PrebananaAbstractCodeOperations
import BANANA.NonPrecompact.PrebananaAbstractCodeEquivalence
import BANANA.NonPrecompact.PrebananaAbstractCodeParity

/-!
# Canonical finite pre-BANANA atom codes are faithful

Every nontrivial finite Boolean algebra with a disjoint-additive
F₂ marking and μ(0)=μ(1)=0 has a canonical finite marked atom
presentation. The original Boolean elements are in bijection with
finite sets of enumerated atoms.

This module packages the previously verified bijectivity, Boolean
operations, and parity identities as a faithful marked code. It
provides the exact object-level input needed for the abstract
strong-amalgamation transfer.
-/

namespace SuccessorTree.NonPrecompact

/-- Every finite nontrivial Boolean parity structure is faithfully
represented by the finite marked powerset of its atoms. -/
noncomputable def prebananaCanonicalFaithfulFiniteCode
    (α : Type*) [BooleanAlgebra α] [Fintype α] [Nontrivial α]
    (μ : α → F2)
    (hzero : μ ⊥ = 0)
    (htop : μ ⊤ = 0)
    (hadd : ∀ x y : α, x ⊓ y = ⊥ →
      μ (x ⊔ y) = μ x + μ y) :
    PrebananaFaithfulFiniteCode α
      (prebananaAbstractAtomCode α μ hzero htop hadd) μ where
  toFun := prebananaAbstractBooleanCode α
  injective := (prebananaAbstractBooleanCode_bijective α).1
  surjective := (prebananaAbstractBooleanCode_bijective α).2
  map_bot := prebananaAbstractBooleanCode_bot α
  map_top := prebananaAbstractBooleanCode_top α
  map_sup := prebananaAbstractBooleanCode_sup α
  map_inf := prebananaAbstractBooleanCode_inf α
  map_parity := prebananaAbstractBooleanCode_parity
    α μ hzero htop hadd

end SuccessorTree.NonPrecompact
