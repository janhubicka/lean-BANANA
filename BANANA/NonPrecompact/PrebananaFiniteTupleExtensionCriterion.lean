import BANANA.NonPrecompact.PrebananaFiniteOrbitCriterion
import BANANA.NonPrecompact.PrebananaGeneratedMarkedIsomorphism

/-!
# From finite generated marked isomorphisms to finite tuple-orbit quotients

A finite tuple presentation consists of one marked finite Boolean atom
code together with a tuple of Boolean elements of that code. Its
profile records realised membership patterns and the F₂ marking of
each pattern fibre.

The verified generated-marked-isomorphism theorem turns equality of
profiles into a marked isomorphism of tuple-generated subalgebras.
Consequently *any* equivalence relation which identifies tuples
related by these generated isomorphisms has only finitely many classes.

For applications to the pre-BANANA Fraïssé limit, the remaining
hypothesis is the standard ultrahomogeneity extension principle:
a finite generated marked isomorphism extends to an automorphism of
the limit. The infinite limit and this application are deliberately
not asserted by the finite theorem below.
-/

namespace SuccessorTree.NonPrecompact

/-- The concrete data of a finite pre-BANANA tuple, allowing the
ambient marked atom structure to vary. -/
structure PrebananaFiniteTuplePresentation (n : ℕ) where
  code : PrebananaAtomStructure
  tuple : Fin n → Finset (Fin code.atomCount)

/-- The finite marked membership-pattern profile of this tuple. -/
noncomputable def PrebananaFiniteTuplePresentation.profile
    {n : ℕ} (x : PrebananaFiniteTuplePresentation n) :
    Finset (Fin n → Bool) × ((Fin n → Bool) → F2) :=
  prebananaTupleProfile x.code x.tuple

/-- If a relation identifies any two tuples whose finitely
generated marked Boolean algebras are isomorphic by a generator-
preserving isomorphism, it has finitely many quotient classes. -/
theorem prebananaFiniteTuplePresentation_quotient_finite_of_extension
    {n : ℕ}
    [s : Setoid (PrebananaFiniteTuplePresentation n)]
    (hExtension : ∀ x y : PrebananaFiniteTuplePresentation n,
      Nonempty (PrebananaGeneratedMarkedIso
        x.code y.code x.tuple y.tuple) → x ≈ y) :
    Finite (Quotient s) := by
  apply prebananaFiniteProfile_quotient_finite n
    (fun x : PrebananaFiniteTuplePresentation n => x.profile)
  intro x y h
  apply hExtension x y
  exact ⟨prebananaGeneratedMarkedIso_of_profile_eq
    x.code y.code x.tuple y.tuple h⟩

end SuccessorTree.NonPrecompact
