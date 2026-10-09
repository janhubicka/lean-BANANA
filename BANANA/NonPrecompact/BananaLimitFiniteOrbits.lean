import BANANA.NonPrecompact.BananaLimitTupleOrbit
import BANANA.NonPrecompact.FiniteInvariantRepresentatives

/-!
# Finitely many tuple orbits of the countable BANANA pairing

For every choice of left and right tuple lengths, there is a finite
collection of ordered tuple pairs such that every tuple pair is the
image of a representative under a global pairing-preserving
automorphism. This is the oligomorphicity statement needed for the
standard Ryll–Nardzewski deduction of omega-categoricity.

The proof uses completeness of the finite signature consisting of
linear dependency patterns and cross-pairings. Ryll–Nardzewski itself
is a separate general model-theoretic theorem and is not formalised
here.
-/

namespace SuccessorTree.NonPrecompact

/-- An ordered pair of left- and right-sort tuples. -/
abbrev BananaLimitTuplePair (l r : ℕ) : Type :=
  (Fin l → BananaLimitVector) × (Fin r → BananaLimitVector)

/-- Two ordered tuple pairs are related by a global automorphism
of the two-sorted BANANA pairing. -/
def bananaLimitTupleOrbitRelated {l r : ℕ}
    (p q : BananaLimitTuplePair l r) : Prop :=
  ∃ EL ER : BananaLimitVector ≃ₗ[F2] BananaLimitVector,
    (∀ x y : BananaLimitVector,
      bananaLimitPairing (EL x) (ER y) = bananaLimitPairing x y) ∧
    (∀ i, EL (p.1 i) = q.1 i) ∧
    (∀ j, ER (p.2 j) = q.2 j)

/-- Equal finite signatures force actual global-orbit equivalence. -/
theorem bananaLimitTupleOrbitRelated_of_signature_eq
    {l r : ℕ}
    (p q : BananaLimitTuplePair l r)
    (h : bananaLimitTupleSignature p.1 p.2 =
      bananaLimitTupleSignature q.1 q.2) :
    bananaLimitTupleOrbitRelated p q :=
  bananaLimitTupleSignature_complete p.1 q.1 p.2 q.2 h

/-- Every ordered two-sorted tuple pair belongs to the global orbit
of one of finitely many representatives. -/
theorem bananaLimit_exists_finite_tuple_orbit_representatives
    (l r : ℕ) :
    ∃ reps : Finset (BananaLimitTuplePair l r),
      ∀ p : BananaLimitTuplePair l r,
        ∃ q ∈ reps, bananaLimitTupleOrbitRelated p q := by
  classical
  letI : Finite (BananaLimitTupleSignature l r) :=
    bananaLimitTupleSignature_finite l r
  letI : Fintype (BananaLimitTupleSignature l r) :=
    Fintype.ofFinite (BananaLimitTupleSignature l r)
  letI : Inhabited (BananaLimitTuplePair l r) :=
    ⟨(fun _ => 0, fun _ => 0)⟩
  exact exists_finite_representatives_of_invariant
    (fun p : BananaLimitTuplePair l r =>
      bananaLimitTupleSignature p.1 p.2)
    (fun p q : BananaLimitTuplePair l r =>
      bananaLimitTupleOrbitRelated p q)
    (by
      intro p q h
      exact bananaLimitTupleOrbitRelated_of_signature_eq p q h)

end SuccessorTree.NonPrecompact
