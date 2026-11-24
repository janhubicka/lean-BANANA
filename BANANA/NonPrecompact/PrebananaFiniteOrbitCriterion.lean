import BANANA.NonPrecompact.FiniteInvariantRepresentatives
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
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

/-- Pre-BANANA finite tuple profiles have a finite codomain,
so completeness for any equivalence relation implies a finite
number of equivalence classes. -/
theorem prebananaFiniteProfile_quotient_finite
    {X : Type*} [s : Setoid X] (n : ℕ)
    (profile : X →
      Finset (Fin n → Bool) × ((Fin n → Bool) → ZMod 2))
    (hcomplete : ∀ x y : X,
      profile x = profile y → x ≈ y) :
    Finite (Quotient s) :=
  finiteQuotient_of_completeFiniteInvariant profile hcomplete

/-- In particular, if a finite pre-BANANA profile is complete for
the action of a group on n-tuples, the orbit quotient is finite. -/
theorem prebananaFiniteProfile_orbits_finite
    {G X : Type*} [Group G] [MulAction G X]
    (n : ℕ)
    (profile : X →
      Finset (Fin n → Bool) × ((Fin n → Bool) → ZMod 2))
    (hcomplete : ∀ x y : X,
      profile x = profile y → x ∈ MulAction.orbit G y) :
    Finite (MulAction.orbitRel.Quotient G X) := by
  letI : Setoid X := MulAction.orbitRel G X
  exact prebananaFiniteProfile_quotient_finite n profile hcomplete

end SuccessorTree.NonPrecompact
