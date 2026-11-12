import BANANA.NonPrecompact.BananaActualSubpairCoordinates

/-!
# Functoriality of the fixed actual-subpair coordinate presentations

Every pair of actual finite subspaces has one coordinate presentation, fixed
once and for all. An isomorphism of actual subpairs induces an isomorphism of
those presentations. This file proves that this translation respects identity,
composition, inverse, and the two coordinate maps. In particular there is no
choice depending on the individual partial isomorphism.

This module does not assume the pairing is nondegenerate, nor that either
sort has positive dimension.
-/

namespace SuccessorTree.NonPrecompact

/-- Equality of actual matrix isomorphisms is determined by their two
linear equivalences; pairing preservation is proof-irrelevant. -/
theorem BananaMatrixIso.eq_of_components
    {l r l' r' : ℕ}
    {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure l' r'}
    (p q : BananaMatrixIso A B)
    (hL : p.left = q.left) (hR : p.right = q.right) : p = q := by
  cases p with
  | mk pl pr hp =>
    cases q with
    | mk ql qr hq =>
      cases hL
      cases hR
      rfl

namespace BananaActualSubpairIso

variable {l r : ℕ} {A : BananaMatrixStructure l r}
variable {U V W : BananaActualSubpair A}

/-- Identity partial isomorphism of an actual two-sorted subpair. -/
def refl (U : BananaActualSubpair A) : BananaActualSubpairIso U U where
  left := LinearEquiv.refl F2 U.left
  right := LinearEquiv.refl F2 U.right
  pairing_apply := by intro x y; rfl

/-- Compose p:U→V with q:V→W, using the actual restricted pairing. -/
def trans (p : BananaActualSubpairIso U V) (q : BananaActualSubpairIso V W) :
    BananaActualSubpairIso U W where
  left := p.left.trans q.left
  right := p.right.trans q.right
  pairing_apply := by
    intro x y
    exact (q.pairing_apply (p.left x) (p.right y)).trans (p.pairing_apply x y)

/-- The inverse is a pairing-preserving actual partial isomorphism. -/
def symm (p : BananaActualSubpairIso U V) : BananaActualSubpairIso V U where
  left := p.left.symm
  right := p.right.symm
  pairing_apply := by
    intro x y
    have h := p.pairing_apply (p.left.symm x) (p.right.symm y)
    simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- The fixed coordinate maps give the corresponding actual left map. -/
theorem toPresentedIso_left_coordinates
    (p : BananaActualSubpairIso U V)
    (x : Fin U.presentation.leftDim → F2) :
    V.leftCoordinateEquiv (p.toPresentedIso.left x) =
      p.left (U.leftCoordinateEquiv x) := by
  change V.leftCoordinateEquiv
    (V.leftCoordinateEquiv.symm (p.left (U.leftCoordinateEquiv x))) = _
  exact V.leftCoordinateEquiv.apply_symm_apply _

/-- The same compatibility for the actual right map. -/
theorem toPresentedIso_right_coordinates
    (p : BananaActualSubpairIso U V)
    (y : Fin U.presentation.rightDim → F2) :
    V.rightCoordinateEquiv (p.toPresentedIso.right y) =
      p.right (U.rightCoordinateEquiv y) := by
  change V.rightCoordinateEquiv
    (V.rightCoordinateEquiv.symm (p.right (U.rightCoordinateEquiv y))) = _
  exact V.rightCoordinateEquiv.apply_symm_apply _

/-- Transport of the actual identity is the identity matrix isomorphism. -/
theorem toPresentedIso_refl (U : BananaActualSubpair A) :
    (refl U).toPresentedIso = BananaMatrixIso.refl U.presentation.carrier := by
  apply BananaMatrixIso.eq_of_components
  · apply LinearEquiv.ext
    intro x
    change U.leftCoordinateEquiv.symm (U.leftCoordinateEquiv x) = x
    exact U.leftCoordinateEquiv.symm_apply_apply x
  · apply LinearEquiv.ext
    intro y
    change U.rightCoordinateEquiv.symm (U.rightCoordinateEquiv y) = y
    exact U.rightCoordinateEquiv.symm_apply_apply y

/-- The fixed-coordinate translation preserves all composable arrows.
This is the critical functoriality needed by class-indexed coherent EPPA. -/
theorem toPresentedIso_trans
    (p : BananaActualSubpairIso U V) (q : BananaActualSubpairIso V W) :
    (p.trans q).toPresentedIso = p.toPresentedIso.trans q.toPresentedIso := by
  apply BananaMatrixIso.eq_of_components
  · apply LinearEquiv.ext
    intro x
    change W.leftCoordinateEquiv.symm
      (q.left (p.left (U.leftCoordinateEquiv x))) =
      W.leftCoordinateEquiv.symm
        (q.left (V.leftCoordinateEquiv
          (V.leftCoordinateEquiv.symm (p.left (U.leftCoordinateEquiv x)))))
    rw [LinearEquiv.apply_symm_apply]
  · apply LinearEquiv.ext
    intro y
    change W.rightCoordinateEquiv.symm
      (q.right (p.right (U.rightCoordinateEquiv y))) =
      W.rightCoordinateEquiv.symm
        (q.right (V.rightCoordinateEquiv
          (V.rightCoordinateEquiv.symm (p.right (U.rightCoordinateEquiv y)))))
    rw [LinearEquiv.apply_symm_apply]

/-- Inverting an actual partial isomorphism commutes with taking its fixed
matrix-coordinate code. -/
theorem toPresentedIso_symm (p : BananaActualSubpairIso U V) :
    p.symm.toPresentedIso = p.toPresentedIso.symm := by
  apply BananaMatrixIso.eq_of_components
  · apply LinearEquiv.ext
    intro x
    change U.leftCoordinateEquiv.symm (p.left.symm (V.leftCoordinateEquiv x)) =
      U.leftCoordinateEquiv.symm (p.left.symm (V.leftCoordinateEquiv x))
    rfl
  · apply LinearEquiv.ext
    intro y
    change U.rightCoordinateEquiv.symm (p.right.symm (V.rightCoordinateEquiv y)) =
      U.rightCoordinateEquiv.symm (p.right.symm (V.rightCoordinateEquiv y))
    rfl

end BananaActualSubpairIso

/-- The left coordinate identification has exactly the original image. -/
theorem BananaActualSubpair.leftCoordinateEquiv_val
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U : BananaActualSubpair A)
    (x : Fin U.presentation.leftDim → F2) :
    (U.leftCoordinateEquiv x).val = U.presentation.inclusion.left x := rfl

/-- The right coordinate identification has exactly the original image. -/
theorem BananaActualSubpair.rightCoordinateEquiv_val
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U : BananaActualSubpair A)
    (y : Fin U.presentation.rightDim → F2) :
    (U.rightCoordinateEquiv y).val = U.presentation.inclusion.right y := rfl

end SuccessorTree.NonPrecompact
