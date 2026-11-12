import BANANA.NonPrecompact.FolkmanFirstOrderSubstructure

/-!
# Tagged first-order substructures are pairs of native non-unital subrings

On a finite Boolean-ring pairing, a substructure of the tagged
single-sorted first-order encoding cannot omit either named zero
and is closed under the two ring operations on each sort.

The intersections with the left and right carriers are therefore
non-unital subrings. In a Boolean ring, additive inversion is the
identity and needs no extra named symbol. Thus every first-order
substructure is EXACTLY the tagged union of its two original
non-unital subrings.

The BooleanRing assumptions here are important: for an arbitrary
non-unital ring without characteristic two, closure under zero,
addition and multiplication alone need not imply closure under
additive inverses. For a Folkman countable limit, characteristic
two is a separate consequence of finite-stage coverage.

No global multiplicative unit is added to the language.
-/

namespace SuccessorTree.NonPrecompact

open scoped FirstOrder

/-- Recover the left original non-unital subring of a tagged
first-order substructure of finite Boolean rings. -/
noncomputable def folkmanLeftSubringOfFirstOrder
    {L R : Type*} [BooleanRing L] [BooleanRing R]
    (β : L → R → F2)
    (S : @FirstOrder.Language.Substructure folkmanFirstOrderLanguage
      (Sum L R) (folkmanTaggedFirstOrderStructure L R β)) :
    NonUnitalSubring L := by
  classical
  letI : folkmanFirstOrderLanguage.Structure (Sum L R) :=
    folkmanTaggedFirstOrderStructure L R β
  refine {
    carrier := {x : L | (Sum.inl x : Sum L R) ∈ S}
    zero_mem' := ?_
    add_mem' := ?_
    mul_mem' := ?_
    neg_mem' := ?_
  }
  · have h := S.fun_mem
      (0 : folkmanFirstOrderLanguage.Functions 0)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
    change (Sum.inl (0 : L) : Sum L R) ∈ S at h
    exact h
  · intro x y hx hy
    let args : Fin 2 → Sum L R :=
      fun i => if i = 0 then .inl x else .inl y
    have ha : ∀ i, args i ∈ S := by
      intro i
      fin_cases i
      · simpa [args] using hx
      · simpa [args] using hy
    have h := S.fun_mem
      (0 : folkmanFirstOrderLanguage.Functions 2) args ha
    change (Sum.inl (x + y) : Sum L R) ∈ S at h
    exact h
  · intro x y hx hy
    let args : Fin 2 → Sum L R :=
      fun i => if i = 0 then .inl x else .inl y
    have ha : ∀ i, args i ∈ S := by
      intro i
      fin_cases i
      · simpa [args] using hx
      · simpa [args] using hy
    have h := S.fun_mem
      (1 : folkmanFirstOrderLanguage.Functions 2) args ha
    change (Sum.inl (x * y) : Sum L R) ∈ S at h
    exact h
  · intro x hx
    simpa only [BooleanRing.neg_eq] using hx

/-- Recover the right original non-unital subring from the same
tagged first-order substructure. -/
noncomputable def folkmanRightSubringOfFirstOrder
    {L R : Type*} [BooleanRing L] [BooleanRing R]
    (β : L → R → F2)
    (S : @FirstOrder.Language.Substructure folkmanFirstOrderLanguage
      (Sum L R) (folkmanTaggedFirstOrderStructure L R β)) :
    NonUnitalSubring R := by
  classical
  letI : folkmanFirstOrderLanguage.Structure (Sum L R) :=
    folkmanTaggedFirstOrderStructure L R β
  refine {
    carrier := {y : R | (Sum.inr y : Sum L R) ∈ S}
    zero_mem' := ?_
    add_mem' := ?_
    mul_mem' := ?_
    neg_mem' := ?_
  }
  · have h := S.fun_mem
      (1 : folkmanFirstOrderLanguage.Functions 0)
      (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i)
    change (Sum.inr (0 : R) : Sum L R) ∈ S at h
    exact h
  · intro x y hx hy
    let args : Fin 2 → Sum L R :=
      fun i => if i = 0 then .inr x else .inr y
    have ha : ∀ i, args i ∈ S := by
      intro i
      fin_cases i
      · simpa [args] using hx
      · simpa [args] using hy
    have h := S.fun_mem
      (2 : folkmanFirstOrderLanguage.Functions 2) args ha
    change (Sum.inr (x + y) : Sum L R) ∈ S at h
    exact h
  · intro x y hx hy
    let args : Fin 2 → Sum L R :=
      fun i => if i = 0 then .inr x else .inr y
    have ha : ∀ i, args i ∈ S := by
      intro i
      fin_cases i
      · simpa [args] using hx
      · simpa [args] using hy
    have h := S.fun_mem
      (3 : folkmanFirstOrderLanguage.Functions 2) args ha
    change (Sum.inr (x * y) : Sum L R) ∈ S at h
    exact h
  · intro y hy
    simpa only [BooleanRing.neg_eq] using hy

/-- Every tagged first-order substructure of finite Boolean-ring
pairings is exactly the union of the two native non-unital
subrings recovered from its left and right carriers.

In particular, there are no spurious first-order substructures
introduced by the wrong-sort totalisation of operations. -/
theorem folkmanTaggedSubstructure_recover
    {L R : Type*} [BooleanRing L] [BooleanRing R]
    (β : L → R → F2)
    (S : @FirstOrder.Language.Substructure folkmanFirstOrderLanguage
      (Sum L R) (folkmanTaggedFirstOrderStructure L R β)) :
    folkmanTaggedSubstructure β
        (folkmanLeftSubringOfFirstOrder β S)
        (folkmanRightSubringOfFirstOrder β S) = S := by
  apply SetLike.ext
  intro x
  cases x with
  | inl a => rfl
  | inr b => rfl

end SuccessorTree.NonPrecompact
