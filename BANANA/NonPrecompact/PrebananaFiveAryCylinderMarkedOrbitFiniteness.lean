import BANANA.NonPrecompact.PrebananaFiveAryCylinderTupleProfileCompleteness
import BANANA.NonPrecompact.PrebananaFiniteOrbitCriterion

/-!
# Finite marked automorphism-orbit quotients of countable cylinders

The marked automorphism-orbit equivalence relation on finite tuples
is defined by the existence of a *global* Boolean order
automorphism preserving the F₂ marking and mapping all coordinates.

The already verified finite profile criterion applies once equal
finite marked profiles are known to imply equivalence under that
relation. The latter implication is proved in the preceding module
under an explicit ultrahomogeneity hypothesis.

The conclusion below is deliberately conditional; the explicit
countable pre-BANANA ultrahomogeneity theorem is formalised separately.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Orbit equivalence of finite tuples under genuine
global marking-preserving Boolean automorphisms. -/
noncomputable def prebananaCylinderMarkedOrbitSetoid (n : ℕ) :
    Setoid (Fin n → PrebananaFiveAryCylinderLimitCarrier) where
  r xs ys :=
    ∃ E : PrebananaFiveAryCylinderLimitCarrier ≃o
        PrebananaFiveAryCylinderLimitCarrier,
      (∀ x : PrebananaFiveAryCylinderLimitCarrier,
        prebananaFiveAryCylinderMark (E x) =
          prebananaFiveAryCylinderMark x) ∧
      ∀ i : Fin n, E (xs i) = ys i
  iseqv := by
    constructor
    · intro xs
      refine ⟨OrderIso.refl _, ?_, ?_⟩
      · intro x
        rfl
      · intro i
        rfl
    · intro xs ys h
      obtain ⟨E, hmark, hcoord⟩ := h
      refine ⟨E.symm, ?_, ?_⟩
      · intro x
        have h := hmark (E.symm x)
        simpa only [OrderIso.apply_symm_apply] using h.symm
      · intro i
        simpa only [OrderIso.symm_apply_apply] using
          (congrArg E.symm (hcoord i)).symm
    · intro xs ys zs hxy hyz
      obtain ⟨E, hEμ, hE⟩ := hxy
      obtain ⟨F, hFμ, hF⟩ := hyz
      refine ⟨E.trans F, ?_, ?_⟩
      · intro x
        exact (hFμ (E x)).trans (hEμ x)
      · intro i
        change F (E (xs i)) = zs i
        rw [hE i, hF i]

/-- Assuming the exact global marked automorphism extension property,
the countable cylinder algebra has finitely many marked automorphism
orbits on tuples of every fixed finite length. -/
theorem prebananaCylinderMarkedOrbit_finite_of_homogeneity
    (hhom :
      ∀ (A : PrebananaFiniteBooleanModel)
        (i j : PrebananaFiniteToCountableEmbedding
          A prebananaCylinderCountableModel),
        ∃ E : PrebananaFiveAryCylinderLimitCarrier ≃o
            PrebananaFiveAryCylinderLimitCarrier,
          (∀ x : PrebananaFiveAryCylinderLimitCarrier,
            prebananaFiveAryCylinderMark (E x) =
              prebananaFiveAryCylinderMark x) ∧
          ∀ a : A.carrier, E (i.hom a) = j.hom a)
    (n : ℕ) :
    Finite (Quotient (prebananaCylinderMarkedOrbitSetoid n)) := by
  letI : Setoid (Fin n → PrebananaFiveAryCylinderLimitCarrier) :=
    prebananaCylinderMarkedOrbitSetoid n
  exact prebananaFiniteProfile_quotient_finite n
    prebananaCylinderTupleProfile
    (fun xs ys hp =>
      prebananaCylinder_profile_eq_implies_automorphism hhom xs ys hp)

end SuccessorTree.NonPrecompact
