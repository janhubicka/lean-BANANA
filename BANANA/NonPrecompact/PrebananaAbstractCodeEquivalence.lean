import BANANA.NonPrecompact.PrebananaAbstractCodeParity

/-!
# The atom code of every abstract finite Boolean element is a bijection

An arbitrary finite Boolean algebra is canonically the powerset of
its abstract atoms. Its explicit Fin-indexed element code is a
bijection, not merely an injective representation. This is needed
to lift common elements supplied by the powerset strong-amalgamation
theorem back to the original finite Boolean algebra.

The code is defined in `PrebananaAbstractCodeParity`; its
bijectivity is a purely Boolean-algebraic statement independent
of the marking.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- The full Boolean element code as a genuine equivalence. -/
noncomputable def prebananaAbstractBooleanCodeEquiv
    (α : Type*) [BooleanAlgebra α] [Fintype α] :
    α ≃ Finset (Fin (Fintype.card (PrebananaAbstractAtoms α))) :=
  (prebananaFiniteBooleanAtomFinsetOrderIso α).toEquiv.trans
    ((prebananaAbstractAtomIndex α).symm.finsetCongr)

/-- This equivalence agrees exactly with the original finite
element-code function used for pre-BANANA parity. -/
theorem prebananaAbstractBooleanCodeEquiv_apply
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (x : α) :
    prebananaAbstractBooleanCodeEquiv α x =
      prebananaAbstractBooleanCode α x := by
  classical
  change
    ((prebananaFiniteBooleanAtomFinsetOrderIso α) x).map
      (prebananaAbstractAtomIndex α).symm.toEmbedding =
    ((prebananaFiniteBooleanAtomFinsetOrderIso α) x).image
      (prebananaAbstractAtomIndex α).symm
  exact Finset.map_eq_image _ _

/-- Every finite atom-subset code corresponds to a unique element
of the original Boolean algebra. -/
theorem prebananaAbstractBooleanCode_bijective
    (α : Type*) [BooleanAlgebra α] [Fintype α] :
    Function.Bijective (prebananaAbstractBooleanCode α) := by
  have heq :
      prebananaAbstractBooleanCode α =
        (prebananaAbstractBooleanCodeEquiv α :
          α → Finset (Fin (Fintype.card (PrebananaAbstractAtoms α)))) := by
    funext x
    exact (prebananaAbstractBooleanCodeEquiv_apply α x).symm
  rw [heq]
  exact (prebananaAbstractBooleanCodeEquiv α).bijective

/-- The surjectivity direction needed for strong amalgamation:
each common finite atom subset has an abstract Boolean preimage. -/
theorem prebananaAbstractBooleanCode_surjective
    (α : Type*) [BooleanAlgebra α] [Fintype α] :
    Function.Surjective (prebananaAbstractBooleanCode α) :=
  (prebananaAbstractBooleanCode_bijective α).2

end SuccessorTree.NonPrecompact
