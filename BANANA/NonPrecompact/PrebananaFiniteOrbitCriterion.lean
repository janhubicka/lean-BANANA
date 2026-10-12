import BANANA.NonPrecompact.PrebananaTupleSignatures
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Finite orbit criterion from a complete pre-BANANA tuple profile

A tuple of length n has one of finitely many possible membership
profiles, including the F₂ marking on every membership-pattern fibre.
If equal profiles force two tuples to lie in the same automorphism
orbit, then there are only finitely many orbits.

This module proves that last, elementary quotient argument. The
completion implication is an explicit hypothesis; establishing it
for the Fraïssé limit uses finite marked subalgebra isomorphisms and
ultrahomogeneity. Neither is silently assumed here.
-/

namespace SuccessorTree.NonPrecompact

/-- A finite complete invariant makes the quotient by any
setoid finite. No converse invariance hypothesis is needed. -/
theorem finiteQuotient_of_completeFiniteInvariant
    {X P : Type*} [s : Setoid X] [Finite P]
    (profile : X → P)
    (hcomplete : ∀ x y : X,
      profile x = profile y → x ≈ y) :
    Finite (Quotient s) := by
  classical
  let profileOnQuotient : Quotient s → P :=
    fun q => profile q.out
  have hinj : Function.Injective profileOnQuotient := by
    intro q r h
    have hqr : q.out ≈ r.out := hcomplete _ _ h
    calc
      q = (⟦q.out⟧ : Quotient s) := (Quotient.out_eq q).symm
      _ = (⟦r.out⟧ : Quotient s) := Quotient.sound hqr
      _ = r := Quotient.out_eq r
  exact Finite.of_injective profileOnQuotient hinj

/-- Pre-BANANA finite tuple profiles have a finite codomain,
so completeness for any equivalence relation implies a finite
number of equivalence classes. -/
theorem prebananaFiniteProfile_quotient_finite
    {X : Type*} [s : Setoid X] (n : ℕ)
    (profile : X →
      Finset (Fin n → Bool) × ((Fin n → Bool) → F2))
    (hcomplete : ∀ x y : X,
      profile x = profile y → x ≈ y) :
    Finite (Quotient s) := by
  letI : Finite
      (Finset (Fin n → Bool) × ((Fin n → Bool) → F2)) :=
    prebananaTupleProfiles_finite n
  exact finiteQuotient_of_completeFiniteInvariant profile hcomplete

/-- In particular, if a finite pre-BANANA profile is complete for
the action of a group on n-tuples, the orbit quotient is finite. -/
theorem prebananaFiniteProfile_orbits_finite
    {G X : Type*} [Group G] [MulAction G X]
    (n : ℕ)
    (profile : X →
      Finset (Fin n → Bool) × ((Fin n → Bool) → F2))
    (hcomplete : ∀ x y : X,
      profile x = profile y → x ∈ MulAction.orbit G y) :
    Finite (MulAction.orbitRel.Quotient G X) := by
  letI : Setoid X := MulAction.orbitRel G X
  exact prebananaFiniteProfile_quotient_finite n profile hcomplete

end SuccessorTree.NonPrecompact
