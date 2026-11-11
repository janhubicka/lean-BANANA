import Mathlib.GroupTheory.Perm.Basic

/-!
# Codes for two-sorted changes of finite representatives

Choose, for each object U of one isomorphism type, equivalences from a
fixed two-sorted representative to its carriers.  Any isomorphism p : U → V
then determines the automorphism i_V^{-1} p i_U of that representative.
The identity and composition laws are automatic and use the order of
permutation multiplication, not the order of Equiv.trans.

The abstract carriers in this file have no BANANA pairing or linear
structure.  To use these codes in coherent EPPA one must separately
prove that the chosen equivalences and p preserve the pairing and
linear operations, so their codes lie in the appropriate subgroup.
-/

namespace SuccessorTree.NonPrecompact

/-- An isomorphism of two abstract carrier sorts.  Structure
preservation (linearity and pairing) must be imposed separately. -/
structure TwoSortRepresentativeIso
    {O : Type*} (L R : O → Type*) (U V : O) where
  left : L U ≃ L V
  right : R U ≃ R V

namespace TwoSortRepresentativeIso

/-- Identity isomorphism on an object. -/
def refl {O : Type*} {L R : O → Type*} (U : O) :
    TwoSortRepresentativeIso L R U U :=
  ⟨Equiv.refl (L U), Equiv.refl (R U)⟩

/-- Composition p followed by q. -/
def trans {O : Type*} {L R : O → Type*}
    {U V W : O}
    (p : TwoSortRepresentativeIso L R U V)
    (q : TwoSortRepresentativeIso L R V W) :
    TwoSortRepresentativeIso L R U W :=
  ⟨p.left.trans q.left, p.right.trans q.right⟩

/-- Inverse isomorphism, on both sorts. -/
def symm {O : Type*} {L R : O → Type*}
    {U V : O} (p : TwoSortRepresentativeIso L R U V) :
    TwoSortRepresentativeIso L R V U :=
  ⟨p.left.symm, p.right.symm⟩

end TwoSortRepresentativeIso

/-- Encode a two-sorted isomorphism using fixed representative
coordinates on each object. -/
def twoSortRepresentativeCode
    {O : Type*} {L R : O → Type*} {P Q : Type*}
    (iL : ∀ U, P ≃ L U) (iR : ∀ U, Q ≃ R U)
    {U V : O} (p : TwoSortRepresentativeIso L R U V) :
    Equiv.Perm P × Equiv.Perm Q :=
  ⟨((iL U).trans p.left).trans (iL V).symm,
   ((iR U).trans p.right).trans (iR V).symm⟩

/-- The code of an identity is the two-sorted identity. -/
theorem twoSortRepresentativeCode_refl
    {O : Type*} {L R : O → Type*} {P Q : Type*}
    (iL : ∀ U, P ≃ L U) (iR : ∀ U, Q ≃ R U)
    (U : O) :
    twoSortRepresentativeCode iL iR
      (TwoSortRepresentativeIso.refl (L := L) (R := R) U) = 1 := by
  apply Prod.ext
  · apply Equiv.Perm.ext
    intro x
    simp [twoSortRepresentativeCode, TwoSortRepresentativeIso.refl]
  · apply Equiv.Perm.ext
    intro y
    simp [twoSortRepresentativeCode, TwoSortRepresentativeIso.refl]

/-- Codes compose as permutations: code(q after p) = code(q) * code(p).
This explicit order is necessary when applying conjugatedTransport_mul. -/
theorem twoSortRepresentativeCode_trans
    {O : Type*} {L R : O → Type*} {P Q : Type*}
    (iL : ∀ U, P ≃ L U) (iR : ∀ U, Q ≃ R U)
    {U V W : O}
    (p : TwoSortRepresentativeIso L R U V)
    (q : TwoSortRepresentativeIso L R V W) :
    twoSortRepresentativeCode iL iR (p.trans q) =
      twoSortRepresentativeCode iL iR q *
        twoSortRepresentativeCode iL iR p := by
  apply Prod.ext
  · apply Equiv.Perm.ext
    intro x
    simp [twoSortRepresentativeCode, TwoSortRepresentativeIso.trans,
      Equiv.Perm.mul_apply]
  · apply Equiv.Perm.ext
    intro y
    simp [twoSortRepresentativeCode, TwoSortRepresentativeIso.trans,
      Equiv.Perm.mul_apply]


/-- If the chosen representative identifications and the transported
isomorphism preserve the same two-sorted pairing, then so does the
coordinate code on the representative. This statement does not claim
linearity of the coordinate code. -/
theorem twoSortRepresentativeCode_preserves_pairing
    {O : Type*} {L R : O → Type*} {P Q Z : Type*}
    (pair : ∀ U : O, L U → R U → Z)
    (pair₀ : P → Q → Z)
    (iL : ∀ U, P ≃ L U) (iR : ∀ U, Q ≃ R U)
    (hi : ∀ (U : O) (x : P) (y : Q),
      pair U (iL U x) (iR U y) = pair₀ x y)
    {U V : O}
    (p : TwoSortRepresentativeIso L R U V)
    (hp : ∀ x y, pair V (p.left x) (p.right y) = pair U x y) :
    ∀ x y,
      pair₀ ((twoSortRepresentativeCode iL iR p).1 x)
        ((twoSortRepresentativeCode iL iR p).2 y) =
        pair₀ x y := by
  intro x y
  let c := twoSortRepresentativeCode iL iR p
  change pair₀ (c.1 x) (c.2 y) = pair₀ x y
  have hL : (iL V) (c.1 x) = p.left (iL U x) := by
    simp [c, twoSortRepresentativeCode]
  have hR : (iR V) (c.2 y) = p.right (iR U y) := by
    simp [c, twoSortRepresentativeCode]
  calc
    pair₀ (c.1 x) (c.2 y) =
        pair V (iL V (c.1 x)) (iR V (c.2 y)) :=
      (hi V (c.1 x) (c.2 y)).symm
    _ = pair V (p.left (iL U x)) (p.right (iR U y)) := by
      rw [hL, hR]
    _ = pair U (iL U x) (iR U y) := hp _ _
    _ = pair₀ x y := hi U x y

end SuccessorTree.NonPrecompact
