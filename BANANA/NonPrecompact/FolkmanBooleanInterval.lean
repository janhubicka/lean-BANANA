import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.RingTheory.NonUnitalSubring.Basic

/-!
# Unital Boolean intervals in a non-unital Boolean ring

For an idempotent element a, the elements satisfying x*a=x form a ring
with unit a. This is the bounded Boolean interval used for the Stone
action of the point stabilizer in Folkman–BANANA.
-/

namespace SuccessorTree.NonPrecompact

variable {R : Type*} [NonUnitalCommRing R]

/-- The elements contained in an idempotent element, as a non-unital subring. -/
def folkmanBooleanInterval (a : R) : NonUnitalSubring R where
  carrier := {x | x * a = x}
  zero_mem' := zero_mul _
  add_mem' hx hy := by
    change _ * a = _ at hx hy ⊢
    rw [add_mul, hx, hy]
  mul_mem' hx hy := by
    change _ * a = _ at hx hy ⊢
    rw [mul_assoc, hy]
  neg_mem' hx := by
    change _ * a = _ at hx ⊢
    rw [neg_mul, hx]

/-- Adding the interval top as its unit gives the usual Boolean ring.
The addition and multiplication are inherited from the original ring. -/
@[instance_reducible]
def folkmanIntervalBooleanRing (hR : ∀ x : R, x * x = x) (a : R) :
    BooleanRing (folkmanBooleanInterval a) where
  __ := (inferInstance : NonUnitalCommRing (folkmanBooleanInterval a))
  one := ⟨a, hR a⟩
  one_mul x := Subtype.ext (by change a * x.val = x.val; rw [mul_comm]; exact x.property)
  mul_one x := Subtype.ext x.property
  natCast n := n • (⟨a, hR a⟩ : folkmanBooleanInterval a)
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul (⟨a, hR a⟩ : folkmanBooleanInterval a) n
  intCast n := n • (⟨a, hR a⟩ : folkmanBooleanInterval a)
  intCast_ofNat n := natCast_zsmul (⟨a, hR a⟩ : folkmanBooleanInterval a) n
  intCast_negSucc n := negSucc_zsmul (⟨a, hR a⟩ : folkmanBooleanInterval a) n
  isIdempotentElem x := Subtype.ext (hR x.val)

-- The next three lemmas make the order and ring coercions explicit.
theorem folkmanInterval_mem (a : R) (x : folkmanBooleanInterval a) :
    (x : R) * a = (x : R) := x.property

theorem folkmanInterval_zero_val (a : R) :
    ((0 : folkmanBooleanInterval a) : R) = 0 := rfl

theorem folkmanInterval_one_val (hR : ∀ x : R, x * x = x) (a : R) :
    letI := folkmanIntervalBooleanRing hR a
    ((1 : folkmanBooleanInterval a) : R) = a := rfl

/-- A ring automorphism fixing the unit restricts to an interval automorphism. -/
def folkmanIntervalRingEquiv (a : R) (e : R ≃+* R) (ha : e a = a) :
    folkmanBooleanInterval a ≃+* folkmanBooleanInterval a := by
  let restrict (f : R ≃+* R) (hf : f a = a) (x : folkmanBooleanInterval a) :
      folkmanBooleanInterval a :=
    ⟨f x.val, by
      change f x.val * a = f x.val
      calc
        f x.val * a = f x.val * f a := congrArg (fun t => f x.val * t) hf.symm
        _ = f (x.val * a) := (map_mul f x.val a).symm
        _ = f x.val := congrArg f x.property⟩
  have hs : e.symm a = a := by
    simpa only [RingEquiv.symm_apply_apply] using (congrArg e.symm ha).symm
  refine {
    toFun := restrict e ha
    invFun := restrict e.symm hs
    left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
    right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val)
    map_add' := fun x y => Subtype.ext (map_add e x.val y.val)
    map_mul' := fun x y => Subtype.ext (map_mul e x.val y.val) }

theorem folkmanIntervalRingEquiv_apply (a : R) (e : R ≃+* R) (ha : e a = a)
    (x : folkmanBooleanInterval a) :
    ((folkmanIntervalRingEquiv a e ha x : folkmanBooleanInterval a) : R) = e x.val := rfl

/-- A homomorphism whose source unit maps to a factors through the unital
Boolean interval below a. -/
def folkmanHomIntoInterval {S : Type*} [Ring S]
    (hR : ∀ x : R, x * x = x) (a : R) (f : S →ₙ+* R) (hf : f 1 = a) :
    letI := folkmanIntervalBooleanRing hR a
    S →+* folkmanBooleanInterval a := by
  letI := folkmanIntervalBooleanRing hR a
  refine {
    toFun := fun x => ⟨f x, by change f x * a = f x; rw [← hf, ← map_mul, mul_one]⟩
    map_zero' := Subtype.ext (map_zero f)
    map_one' := Subtype.ext hf
    map_add' := fun x y => Subtype.ext (map_add f x y)
    map_mul' := fun x y => Subtype.ext (map_mul f x y) }

theorem folkmanHomIntoInterval_apply {S : Type*} [Ring S]
    (hR : ∀ x : R, x * x = x) (a : R) (f : S →ₙ+* R) (hf : f 1 = a)
    (x : S) :
    letI := folkmanIntervalBooleanRing hR a
    ((folkmanHomIntoInterval hR a f hf x : folkmanBooleanInterval a) : R) = f x := rfl

end SuccessorTree.NonPrecompact
