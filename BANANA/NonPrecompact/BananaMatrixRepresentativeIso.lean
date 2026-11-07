import BANANA.NonPrecompact.BananaMatrixAutGroup
import BANANA.NonPrecompact.CoherentRepresentativeCore

/-!
# Linear, pairing-preserving representative coordinates

Unlike an arbitrary pair of carrier permutations, a BananaMatrixIso records
linearity and pairing preservation. Its representative code therefore lies
in the actual finite BANANA automorphism group, not merely in a product of
symmetric groups. Dimensions may vary with the object; a chosen isomorphism
supplies the necessary equalities without making them extra hypotheses.

The representative identifications are still supplied as data. This module
does not select one representative of every substructure isomorphism type.
-/

namespace SuccessorTree.NonPrecompact

/-- A two-sorted linear isomorphism preserving the original pairing. -/
structure BananaMatrixIso {l r l' r' : ℕ}
    (A : BananaMatrixStructure l r) (B : BananaMatrixStructure l' r') where
  left : (Fin l → F2) ≃ₗ[F2] (Fin l' → F2)
  right : (Fin r → F2) ≃ₗ[F2] (Fin r' → F2)
  pairing_apply : ∀ x y, B.eval (left x) (right y) = A.eval x y

namespace BananaMatrixIso

variable {l r l' r' l'' r'' : ℕ}
variable {A : BananaMatrixStructure l r} {B : BananaMatrixStructure l' r'}
variable {C : BananaMatrixStructure l'' r''}

/-- The identity isomorphism, including zero-dimensional sorts. -/
def refl (A : BananaMatrixStructure l r) : BananaMatrixIso A A where
  left := LinearEquiv.refl F2 (Fin l → F2)
  right := LinearEquiv.refl F2 (Fin r → F2)
  pairing_apply := by intros; rfl

/-- Apply p first and q second. -/
def trans (p : BananaMatrixIso A B) (q : BananaMatrixIso B C) :
    BananaMatrixIso A C where
  left := p.left.trans q.left
  right := p.right.trans q.right
  pairing_apply := by
    intro x y
    exact (q.pairing_apply (p.left x) (p.right y)).trans (p.pairing_apply x y)

/-- Inverse preservation follows from preservation by p. -/
def symm (p : BananaMatrixIso A B) : BananaMatrixIso B A where
  left := p.left.symm
  right := p.right.symm
  pairing_apply := by
    intro x y
    have h := p.pairing_apply (p.left.symm x) (p.right.symm y)
    simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- Forget only surjectivity; keep both linear maps and pairing preservation. -/
def toEmbedding (p : BananaMatrixIso A B) : BananaMatrixEmbedding A B where
  left := p.left.toLinearMap
  right := p.right.toLinearMap
  left_injective := p.left.injective
  right_injective := p.right.injective
  pairing_apply := p.pairing_apply

/-- A self-isomorphism belongs to the concrete pairing-preserving subgroup. -/
def toAutGroup (p : BananaMatrixIso A A) : BananaMatrixAutGroup A :=
  ⟨⟨p.left, p.right⟩, p.pairing_apply⟩

end BananaMatrixIso

section Representatives

variable {O : Type*} {l r : ℕ} {dL dR : O → ℕ}
variable {A : BananaMatrixStructure l r}
variable {B : ∀ U : O, BananaMatrixStructure (dL U) (dR U)}

/-- The actual BANANA automorphism i_V^{-1} p i_U of a representative. -/
def bananaMatrixRepresentativeCode
    (i : ∀ U, BananaMatrixIso A (B U)) {U V : O}
    (p : BananaMatrixIso (B U) (B V)) : BananaMatrixAutGroup A :=
  (((i U).trans p).trans (i V).symm).toAutGroup

/-- Compatibility with the earlier carrier-level coordinate code. -/
theorem bananaMatrixRepresentativeCode_toPerm
    (i : ∀ U, BananaMatrixIso A (B U)) {U V : O}
    (p : BananaMatrixIso (B U) (B V)) :
    ((bananaMatrixRepresentativeCode i p).1.1.toEquiv,
      (bananaMatrixRepresentativeCode i p).1.2.toEquiv) =
      twoSortRepresentativeCode
        (fun U => (i U).left.toEquiv) (fun U => (i U).right.toEquiv)
        (⟨p.left.toEquiv, p.right.toEquiv⟩ :
          TwoSortRepresentativeIso (fun U => Fin (dL U) → F2)
            (fun U => Fin (dR U) → F2) U V) := rfl

/-- The representative code realises p on the left. -/
theorem bananaMatrixRepresentativeCode_left
    (i : ∀ U, BananaMatrixIso A (B U)) {U V : O}
    (p : BananaMatrixIso (B U) (B V)) (x : Fin l → F2) :
    (i V).left ((bananaMatrixRepresentativeCode i p).1.1 x) =
      p.left ((i U).left x) := by
  change (i V).left ((i V).left.symm (p.left ((i U).left x))) = _
  exact (i V).left.apply_symm_apply _

/-- The same code realises p on the right. -/
theorem bananaMatrixRepresentativeCode_right
    (i : ∀ U, BananaMatrixIso A (B U)) {U V : O}
    (p : BananaMatrixIso (B U) (B V)) (y : Fin r → F2) :
    (i V).right ((bananaMatrixRepresentativeCode i p).1.2 y) =
      p.right ((i U).right y) := by
  change (i V).right ((i V).right.symm (p.right ((i U).right y))) = _
  exact (i V).right.apply_symm_apply _

/-- The code of the identity is the identity in Aut(A). -/
theorem bananaMatrixRepresentativeCode_refl
    (i : ∀ U, BananaMatrixIso A (B U)) (U : O) :
    bananaMatrixRepresentativeCode i (BananaMatrixIso.refl (B U)) = 1 := by
  apply Subtype.ext
  apply Prod.ext
  · apply LinearEquiv.ext
    intro x
    change (i U).left.symm ((i U).left x) = x
    exact (i U).left.symm_apply_apply x
  · apply LinearEquiv.ext
    intro y
    change (i U).right.symm ((i U).right y) = y
    exact (i U).right.symm_apply_apply y

/-- Composition in the actual group has the order code(q) * code(p). -/
theorem bananaMatrixRepresentativeCode_trans
    (i : ∀ U, BananaMatrixIso A (B U)) {U V W : O}
    (p : BananaMatrixIso (B U) (B V)) (q : BananaMatrixIso (B V) (B W)) :
    bananaMatrixRepresentativeCode i (p.trans q) =
      bananaMatrixRepresentativeCode i q * bananaMatrixRepresentativeCode i p := by
  apply Subtype.ext
  apply Prod.ext
  · apply LinearEquiv.ext
    intro x
    change (i W).left.symm (q.left (p.left ((i U).left x))) =
      (i W).left.symm (q.left ((i V).left
        ((i V).left.symm (p.left ((i U).left x)))))
    rw [LinearEquiv.apply_symm_apply]
  · apply LinearEquiv.ext
    intro y
    change (i W).right.symm (q.right (p.right ((i U).right y))) =
      (i W).right.symm (q.right ((i V).right
        ((i V).right.symm (p.right ((i U).right y)))))
    rw [LinearEquiv.apply_symm_apply]

/-- Inversion agrees with inversion in the concrete automorphism group. -/
theorem bananaMatrixRepresentativeCode_symm
    (i : ∀ U, BananaMatrixIso A (B U)) {U V : O}
    (p : BananaMatrixIso (B U) (B V)) :
    bananaMatrixRepresentativeCode i p.symm =
      (bananaMatrixRepresentativeCode i p)⁻¹ := by
  apply Subtype.ext
  apply Prod.ext
  · apply LinearEquiv.ext
    intro x
    rfl
  · apply LinearEquiv.ext
    intro y
    rfl

end Representatives

end SuccessorTree.NonPrecompact
