import BANANA.NonPrecompact.FolkmanNativeFiniteClassInterface
import BANANA.NonPrecompact.FolkmanAtomCode

/-!
# Native realisations of the countable Folkman atom-code family

Every finite atom code is realised by actual finite Boolean rings, not
merely by sets of atom labels. Conversely, every finite native pairing is
isomorphic to its realisation in the original two-sorted language.

The underlying rings have units, but the language does not name them and
embeddings are still non-unital. A bijective ring isomorphism necessarily
preserves the unit; using `RingEquiv` here adds no condition on embeddings.

This supplies explicit native representatives and arbitrarily large native
objects. It does not construct the countable homogeneous limit, nor prove
that an arbitrary finite non-unital subring has its own Boolean-ring unit.
This new source requires an exact-head Lean build before validation.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff BigOperators


/-- The finite atom-coordinate bijection is an actual ring isomorphism.
This concerns object isomorphisms, not the non-unital embedding convention. -/
noncomputable def folkmanNativeFiniteCodeRingEquiv
    (α : Type*) [BooleanRing α] [Fintype α] :
    α ≃+* FolkmanNativeCodeRing
      (Fintype.card (PrebananaAbstractAtoms (AsBoolAlg α))) where
  toEquiv := (folkmanNativeFiniteRingCodeEquiv α).trans toBoolRing
  map_mul' := by
    intro x y
    change toBoolRing (folkmanNativeFiniteRingCodeEquiv α (x * y)) =
      toBoolRing (folkmanNativeFiniteRingCodeEquiv α x ∩
        folkmanNativeFiniteRingCodeEquiv α y)
    exact congrArg toBoolRing (folkmanNativeFiniteRingCode_mul α x y)
  map_add' := by
    intro x y
    change toBoolRing (folkmanNativeFiniteRingCodeEquiv α (x + y)) =
      toBoolRing (symmDiff (folkmanNativeFiniteRingCodeEquiv α x)
        (folkmanNativeFiniteRingCodeEquiv α y))
    exact congrArg toBoolRing (folkmanNativeFiniteRingCode_add α x y)

/-- Every finite native object is isomorphic to the native realisation
of its atom code, in both ring operations and the entire cross-pairing. -/
noncomputable def folkmanNativeFiniteCodeIso
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (P : FolkmanNativeFinitePairing L R) :
    FolkmanNativeFinitePairingIso P
      (folkmanNativeCodeRealisation (folkmanNativeFinCode P.pairing)) where
  left := folkmanNativeFiniteCodeRingEquiv L
  right := folkmanNativeFiniteCodeRingEquiv R
  preserves_pairing := by
    intro x y
    change (∑ i ∈ folkmanNativeFiniteRingCodeEquiv L x,
        ∑ j ∈ folkmanNativeFiniteRingCodeEquiv R y,
          (folkmanNativeFinCode P.pairing).edge i j) = P.pairing x y
    exact (folkmanNativeFinCode_pairing
      P.pairing P.add_left P.add_right x y).symm

/-- A countably indexed family of actual native objects represents every
finite native Folkman isomorphism type. No uniqueness of codes is claimed:
renumbering atoms can change a code without changing its isomorphism type. -/
theorem folkmanNativeFinite_countable_native_representatives
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (P : FolkmanNativeFinitePairing L R) :
    Countable FolkmanAtomStructure ∧
      ∃ A : FolkmanAtomStructure,
        Nonempty (FolkmanNativeFinitePairingIso P
          (folkmanNativeCodeRealisation A)) := by
  exact ⟨inferInstance, folkmanNativeFinCode P.pairing,
    ⟨folkmanNativeFiniteCodeIso P⟩⟩

/-- Distinct singleton subsets are distinct elements of the native ring. -/
noncomputable def folkmanNativeCodeSingleton (n : ℕ) :
    Fin n ↪ FolkmanNativeCodeRing n where
  toFun := fun i => toBoolRing {i}
  inj' := by
    intro i j h
    have hs : ({i} : Finset (Fin n)) = {j} := congrArg ofBoolRing h
    have hi : i ∈ ({j} : Finset (Fin n)) := hs ▸ Finset.mem_singleton_self i
    simpa only [Finset.mem_singleton] using hi

/-- A lower bound on the number of actual ring elements, not atom codes. -/
theorem folkmanNativeCodeRing_card_ge (n : ℕ) :
    n ≤ Fintype.card (FolkmanNativeCodeRing n) := by
  have h := Fintype.card_le_of_injective
    (folkmanNativeCodeSingleton n) (folkmanNativeCodeSingleton n).injective
  simpa only [Fintype.card_fin] using h

/-- Native finite Folkman objects have arbitrarily large carriers in both
sorts. The witnesses have zero pairing and require no non-degeneracy. -/
theorem folkmanNativeFinite_native_objects_unbounded (n : ℕ) :
    ∃ P : FolkmanNativeFinitePairing
        (FolkmanNativeCodeRing (n + 1)) (FolkmanNativeCodeRing (n + 1)),
      n < Fintype.card (FolkmanNativeCodeRing (n + 1)) ∧
        n < Fintype.card (FolkmanNativeCodeRing (n + 1)) := by
  have hcard : n < Fintype.card (FolkmanNativeCodeRing (n + 1)) :=
    lt_of_lt_of_le (Nat.lt_succ_self n) (folkmanNativeCodeRing_card_ge (n + 1))
  exact ⟨folkmanNativeCodeRealisation
    (FolkmanAtomStructure.zeroPairing (n + 1) (n + 1)), hcard, hcard⟩

end SuccessorTree.NonPrecompact
