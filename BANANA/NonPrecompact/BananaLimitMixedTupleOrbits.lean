import BANANA.NonPrecompact.BananaLimitFiniteOrbits

/-!
# All finite tuples, with arbitrary mixtures of the two BANANA sorts

The existing tuple-orbit theorem describes a pair consisting of a list
of left-sort vectors and a list of right-sort vectors. A tuple in the
ordinary two-sorted language may alternate between the sorts in any
order. This file closes that representational gap without introducing
a new homogeneity argument.

A tagged tuple carries a finite Boolean sort pattern. Replacing
entries in the opposite sort by zero gives two ordinary vector tuples
of the same length. The sort pattern and their previously formalised
tuple signature form a finite invariant. Equal invariants imply
conjugacy by a genuine global, pairing-preserving automorphism.

This is the complete mixed-sort oligomorphicity statement required by
the *standard* Ryll–Nardzewski deduction of omega-categoricity.
The general model-theoretic implication is not formalised here.
-/

namespace SuccessorTree.NonPrecompact

/-- An ordered tuple in the disjoint union of the two vector-space
sorts of the explicit countable BANANA pairing. -/
abbrev BananaLimitTaggedTuple (n : ℕ) : Type :=
  Fin n → Sum BananaLimitVector BananaLimitVector

/-- Record the actual sort of every entry. -/
def bananaLimitTaggedPattern {n : ℕ}
    (t : BananaLimitTaggedTuple n) : Fin n → Bool :=
  fun i => match t i with
    | .inl _ => true
    | .inr _ => false

/-- Extract the left-sort entries, putting zero at right-sort positions. -/
def bananaLimitTaggedLeft {n : ℕ}
    (t : BananaLimitTaggedTuple n) : Fin n → BananaLimitVector :=
  fun i => match t i with
    | .inl x => x
    | .inr _ => 0

/-- Extract the right-sort entries, putting zero at left-sort positions. -/
def bananaLimitTaggedRight {n : ℕ}
    (t : BananaLimitTaggedTuple n) : Fin n → BananaLimitVector :=
  fun i => match t i with
    | .inl _ => 0
    | .inr y => y

/-- The tagged finite signature: an explicit sort pattern together
with the complete two-tuple linear-relation/pairing signature. -/
abbrev BananaLimitTaggedSignature (n : ℕ) : Type :=
  (Fin n → Bool) × BananaLimitTupleSignature n n

/-- There are finitely many mixed-sort signatures of each tuple length. -/
theorem bananaLimitTaggedSignature_finite (n : ℕ) :
    Finite (BananaLimitTaggedSignature n) := by
  letI : Finite (BananaLimitTupleSignature n n) :=
    bananaLimitTupleSignature_finite n n
  infer_instance

/-- The invariant of a tagged tuple, using the existing complete
signature of the two masked coordinate tuples. -/
noncomputable def bananaLimitTaggedSignature {n : ℕ}
    (t : BananaLimitTaggedTuple n) :
    BananaLimitTaggedSignature n :=
  (bananaLimitTaggedPattern t,
   bananaLimitTupleSignature (bananaLimitTaggedLeft t)
     (bananaLimitTaggedRight t))

/-- Act on a single tagged vector using the left or right component
of a pairing-preserving global automorphism. -/
def bananaLimitTaggedAct
    (EL ER : BananaLimitVector ≃ₗ[F2] BananaLimitVector)
    (v : Sum BananaLimitVector BananaLimitVector) :
    Sum BananaLimitVector BananaLimitVector :=
  match v with
  | .inl x => .inl (EL x)
  | .inr y => .inr (ER y)

/-- Two mixed-sort tuples are in one orbit under a *single* global
two-sorted pairing automorphism, with the given coordinate order. -/
def bananaLimitTaggedOrbitRelated {n : ℕ}
    (s t : BananaLimitTaggedTuple n) : Prop :=
  ∃ EL ER : BananaLimitVector ≃ₗ[F2] BananaLimitVector,
    (∀ x y : BananaLimitVector,
      bananaLimitPairing (EL x) (ER y) = bananaLimitPairing x y) ∧
    ∀ i : Fin n, bananaLimitTaggedAct EL ER (s i) = t i

/-- Equality of tagged signatures forces global automorphism
conjugacy. Neither the order nor the sort of any entry can change. -/
theorem bananaLimitTaggedOrbitRelated_of_signature_eq {n : ℕ}
    (s t : BananaLimitTaggedTuple n)
    (h : bananaLimitTaggedSignature s =
      bananaLimitTaggedSignature t) :
    bananaLimitTaggedOrbitRelated s t := by
  have hPattern : bananaLimitTaggedPattern s =
      bananaLimitTaggedPattern t := congrArg Prod.fst h
  have hSignature :
      bananaLimitTupleSignature (bananaLimitTaggedLeft s)
        (bananaLimitTaggedRight s) =
      bananaLimitTupleSignature (bananaLimitTaggedLeft t)
        (bananaLimitTaggedRight t) := congrArg Prod.snd h
  obtain ⟨EL, ER, hPair, hLeft, hRight⟩ :=
    bananaLimitTupleSignature_complete
      (bananaLimitTaggedLeft s) (bananaLimitTaggedLeft t)
      (bananaLimitTaggedRight s) (bananaLimitTaggedRight t)
      hSignature
  refine ⟨EL, ER, hPair, ?_⟩
  intro i
  cases hs : s i with
  | inl x =>
    cases ht : t i with
    | inl y =>
      have hxy : EL x = y := by
        simpa [bananaLimitTaggedLeft, hs, ht] using hLeft i
      simp [bananaLimitTaggedAct, hs, ht, hxy]
    | inr y =>
      have hf : (true : Bool) = false := by
        simpa [bananaLimitTaggedPattern, hs, ht] using
          congrFun hPattern i
      cases hf
  | inr x =>
    cases ht : t i with
    | inl y =>
      have hf : (false : Bool) = true := by
        simpa [bananaLimitTaggedPattern, hs, ht] using
          congrFun hPattern i
      cases hf
    | inr y =>
      have hxy : ER x = y := by
        simpa [bananaLimitTaggedRight, hs, ht] using hRight i
      simp [bananaLimitTaggedAct, hs, ht, hxy]

/-- All tagged tuples of each length fall into the orbits of
finitely many actual tagged representatives. This is the
mixed-sort formulation of oligomorphicity. -/
theorem bananaLimit_exists_finite_tagged_tuple_orbit_representatives
    (n : ℕ) :
    ∃ reps : Finset (BananaLimitTaggedTuple n),
      ∀ t : BananaLimitTaggedTuple n,
        ∃ s ∈ reps, bananaLimitTaggedOrbitRelated t s := by
  classical
  letI : Finite (BananaLimitTaggedSignature n) :=
    bananaLimitTaggedSignature_finite n
  letI : Fintype (BananaLimitTaggedSignature n) :=
    Fintype.ofFinite (BananaLimitTaggedSignature n)
  letI : Inhabited (BananaLimitTaggedTuple n) :=
    ⟨fun _ => .inl 0⟩
  exact exists_finite_representatives_of_invariant
    (fun t : BananaLimitTaggedTuple n =>
      bananaLimitTaggedSignature t)
    (fun t s : BananaLimitTaggedTuple n =>
      bananaLimitTaggedOrbitRelated t s)
    (by
      intro t s h
      exact bananaLimitTaggedOrbitRelated_of_signature_eq t s h)

end SuccessorTree.NonPrecompact
