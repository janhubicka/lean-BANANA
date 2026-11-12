import BANANA.NonPrecompact.BananaStructure
import BANANA.NonPrecompact.FinitePerfectGL
import Mathlib

/-!
# The actual two-sorted finite BANANA automorphism group

For a finite matrix pairing A, take the subgroup of
GL(leftDim,F₂) × GL(rightDim,F₂) whose elements preserve A.eval
on the two sorts simultaneously. This group is finite, including when
one of the vector spaces has dimension zero or the pairing is degenerate.

This supplies the *source group* needed to turn the coherent-completion
action into a genuine group homomorphism. It is distinct from merely
taking all pairs of linear equivalences without the pairing condition.
-/

namespace SuccessorTree.NonPrecompact

/-- The ambient two-sorted linear automorphism group. -/
abbrev BananaMatrixLinearPair (l r : ℕ) : Type :=
  ((Fin l → F2) ≃ₗ[F2] (Fin l → F2)) ×
    ((Fin r → F2) ≃ₗ[F2] (Fin r → F2))

/-- A pairing-preserving pair of linear automorphisms is a subgroup of
the product of the two general linear groups. -/
def bananaMatrixAutSubgroup {l r : ℕ}
    (A : BananaMatrixStructure l r) :
    Subgroup (BananaMatrixLinearPair l r) where
  carrier := {f | ∀ x y, A.eval (f.1 x) (f.2 y) = A.eval x y}
  one_mem' := by
    intro x y
    simp
  mul_mem' := by
    intro f g hf hg x y
    change A.eval ((f.1 * g.1) x) ((f.2 * g.2) y) = A.eval x y
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    exact (hf (g.1 x) (g.2 y)).trans (hg x y)
  inv_mem' := by
    intro f hf x y
    change A.eval ((f.1⁻¹) x) ((f.2⁻¹) y) = A.eval x y
    have h := hf ((f.1⁻¹) x) ((f.2⁻¹) y)
    simpa using h.symm

/-- The concrete finite automorphism group of a finite BANANA pairing. -/
abbrev BananaMatrixAutGroup {l r : ℕ}
    (A : BananaMatrixStructure l r) : Type :=
  ↥(bananaMatrixAutSubgroup A)

/-- Both components of a concrete BANANA automorphism preserve the
original pairing, in the exact standard-coordinate statement. -/
theorem BananaMatrixAutGroup.pairing_apply
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (f : BananaMatrixAutGroup A)
    (x : Fin l → F2) (y : Fin r → F2) :
    A.eval (f.1.1 x) (f.1.2 y) = A.eval x y :=
  f.property x y

/-- Interpret a group element as an embedding of the source structure
to itself, using its linear equivalences on both sorts. -/
def BananaMatrixAutGroup.toEmbedding
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (f : BananaMatrixAutGroup A) :
    BananaMatrixEmbedding A A where
  left := f.1.1.toLinearMap
  right := f.1.2.toLinearMap
  left_injective := f.1.1.injective
  right_injective := f.1.2.injective
  pairing_apply := f.pairing_apply

/-- The two-sorted pairing-preserving automorphism group is finite. -/
instance BananaMatrixAutGroup.instFinite
    {l r : ℕ} (A : BananaMatrixStructure l r) :
    Finite (BananaMatrixAutGroup A) := by
  classical
  infer_instance

end SuccessorTree.NonPrecompact
