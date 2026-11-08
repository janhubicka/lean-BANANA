import BANANA.NonPrecompact.FolkmanNativeFinitePairingClass
import Mathlib.RingTheory.NonUnitalSubring.Defs

/-!
# Hereditary closure in the non-unital Folkman language

A finite substructure need only be closed under zero, addition and
multiplication. It need not contain the ambient multiplicative identity.
We construct its own identity as the finite join of all its elements,
then equip the same carrier and operations with a Boolean-ring structure.
The inclusion remains a non-unital ring homomorphism.

All finite substructures, including the zero subring, are covered. There
is no nonzero-sort assumption and no ambient-unit preservation hypothesis.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

variable {R : Type*} [BooleanRing R]

/-- Closure under the named operations suffices: Boolean-ring negation
is the identity, so no extra negation-closure hypothesis is necessary. -/
def folkmanNativeSubringOfClosed
    (s : Set R) (hzero : (0 : R) ∈ s)
    (hadd : ∀ x y, x ∈ s → y ∈ s → x + y ∈ s)
    (hmul : ∀ x y, x ∈ s → y ∈ s → x * y ∈ s) :
    NonUnitalSubring R where
  carrier := s
  zero_mem' := hzero
  add_mem' := fun hx hy => hadd _ _ hx hy
  mul_mem' := fun hx hy => hmul _ _ hx hy
  neg_mem' := by
    intro x hx
    simpa only [BooleanRing.neg_eq] using hx

/-- A finite join is still in the non-unital subring, since
`x ⊔ y` is the ring term `x + y + x*y`. -/
theorem folkmanNativeSubring_finiteJoin_mem
    (S : NonUnitalSubring R) (t : Finset S) :
    ofBoolAlg (t.sup (fun x : S => toBoolAlg (x : R))) ∈ S := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty, ofBoolAlg_bot] using S.zero_mem
  | @insert x t hx ih =>
      rw [Finset.sup_insert, ofBoolAlg_sup]
      exact S.add_mem (S.add_mem x.property ih) (S.mul_mem x.property ih)

/-- The identity belonging to a finite subring itself, not necessarily
the identity of the ambient ring. -/
noncomputable def folkmanNativeSubringUnit
    (S : NonUnitalSubring R) [Fintype S] : S :=
  ⟨ofBoolAlg (Finset.univ.sup (fun x : S => toBoolAlg (x : R))),
    folkmanNativeSubring_finiteJoin_mem S Finset.univ⟩

/-- The finite join absorbs every subring element under multiplication. -/
theorem folkmanNativeSubring_mul_unit
    (S : NonUnitalSubring R) [Fintype S] (x : S) :
    x * folkmanNativeSubringUnit S = x := by
  classical
  apply Subtype.ext
  change (x : R) *
    ofBoolAlg (Finset.univ.sup (fun y : S => toBoolAlg (y : R))) = x
  exact (ofBoolAlg_mul_ofBoolAlg_eq_left_iff).2
    (Finset.le_sup (f := fun y : S => toBoolAlg (y : R))
      (Finset.mem_univ x))

/-- The same element is a left identity. -/
theorem folkmanNativeSubring_unit_mul
    (S : NonUnitalSubring R) [Fintype S] (x : S) :
    folkmanNativeSubringUnit S * x = x := by
  rw [mul_comm]
  exact folkmanNativeSubring_mul_unit S x

/-- The constructed identity is forced by the unchanged multiplication. -/
theorem folkmanNativeSubring_unit_unique
    (S : NonUnitalSubring R) [Fintype S] (e : S)
    (he : ∀ x : S, e * x = x) :
    e = folkmanNativeSubringUnit S := by
  exact (folkmanNativeSubring_mul_unit S e).symm.trans
    (he (folkmanNativeSubringUnit S))

/-- Ambient-unit preservation is an extra condition, not built into
heredity: it holds precisely when the ambient unit belongs to the subring. -/
theorem folkmanNativeSubring_unit_eq_ambient_iff
    (S : NonUnitalSubring R) [Fintype S] :
    (folkmanNativeSubringUnit S : R) = 1 ↔ (1 : R) ∈ S := by
  constructor
  · intro h
    exact h ▸ (folkmanNativeSubringUnit S).property
  · intro h
    have hu := congrArg (fun x : S => (x : R))
      (folkmanNativeSubring_unit_mul S ⟨1, h⟩)
    change (folkmanNativeSubringUnit S : R) * 1 = 1 at hu
    simpa only [mul_one] using hu

/-- Equip the original subring carrier with its own Boolean-ring unit.
All named operations are inherited unchanged from the ambient ring.
This is a definition, not a new global instance. -/
noncomputable def folkmanNativeSubringBooleanRing
    (S : NonUnitalSubring R) [Fintype S] : BooleanRing S where
  __ := (inferInstance : NonUnitalRing S)
  one := folkmanNativeSubringUnit S
  one_mul := folkmanNativeSubring_unit_mul S
  mul_one := folkmanNativeSubring_mul_unit S
  isIdempotentElem x := by
    change x * x = x
    apply Subtype.ext
    exact BooleanRing.mul_self (x : R)

/-- The inclusion preserves exactly the original non-unital language,
without requiring the new unit to map to the ambient one. -/
noncomputable def folkmanNativeSubringInclusion
    (S : NonUnitalSubring R) [Fintype S] :
    letI := folkmanNativeSubringBooleanRing S
    S →ₙ+* R := by
  letI := folkmanNativeSubringBooleanRing S
  exact {
    toFun := fun x => x.val
    map_zero' := rfl
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl
  }

/-- Restrict a native Folkman structure to any two finite non-unital
subrings. This constructs the Boolean-ring structures that pairing
pullback alone had previously assumed. -/
noncomputable def folkmanNativeFiniteRestriction
    {L R : Type*} [BooleanRing L] [BooleanRing R]
    (P : FolkmanNativeFinitePairing L R)
    (SL : NonUnitalSubring L) (SR : NonUnitalSubring R)
    [Fintype SL] [Fintype SR] :
    letI := folkmanNativeSubringBooleanRing SL
    letI := folkmanNativeSubringBooleanRing SR
    FolkmanNativeFinitePairing SL SR := by
  letI := folkmanNativeSubringBooleanRing SL
  letI := folkmanNativeSubringBooleanRing SR
  exact P.pullback (folkmanNativeSubringInclusion SL)
    (folkmanNativeSubringInclusion SR)

/-- End-to-end native hereditary certificate: the original subtype
inclusions are injective non-unital ring maps and preserve the entire
restricted cross-pairing. No ambient unit belongs to the hypotheses. -/
theorem folkmanNativeFinite_hereditary
    {L R : Type*} [BooleanRing L] [BooleanRing R]
    (P : FolkmanNativeFinitePairing L R)
    (SL : NonUnitalSubring L) (SR : NonUnitalSubring R)
    [Fintype SL] [Fintype SR] :
    letI := folkmanNativeSubringBooleanRing SL
    letI := folkmanNativeSubringBooleanRing SR
    ∃ (Q : FolkmanNativeFinitePairing SL SR)
      (iL : SL →ₙ+* L) (iR : SR →ₙ+* R),
      Function.Injective iL ∧ Function.Injective iR ∧
      (∀ x : SL, iL x = (x : L)) ∧
      (∀ y : SR, iR y = (y : R)) ∧
      (∀ x y, Q.pairing x y = P.pairing (iL x) (iR y)) := by
  letI := folkmanNativeSubringBooleanRing SL
  letI := folkmanNativeSubringBooleanRing SR
  exact ⟨folkmanNativeFiniteRestriction P SL SR,
    folkmanNativeSubringInclusion SL, folkmanNativeSubringInclusion SR,
    Subtype.val_injective, Subtype.val_injective,
    (fun _ => rfl), (fun _ => rfl), (fun _ _ => rfl)⟩

end SuccessorTree.NonPrecompact
