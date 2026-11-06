import BANANA.NonPrecompact.BananaPresentedSubpairAtlas

/-!
# Fixed coordinate presentations of actual two-sorted subspaces

An actual finite BANANA substructure is a pair of vector subspaces.
The hereditary theorem constructs a finite matrix presentation for every
such pair. We choose the presentation once for each actual subpair.

The coordinate maps are genuine linear equivalences onto the prescribed
subspaces. An actual pairing-preserving partial isomorphism therefore
induces a pairing-preserving matrix isomorphism with no additional
compatibility-of-bases hypothesis.

The final groupoid theorem must still transport the class-family action
along these codes and prove composition on actual partial isomorphisms.
-/

namespace SuccessorTree.NonPrecompact

/-- A two-sorted actual substructure of a finite BANANA structure. -/
structure BananaActualSubpair {l r : ℕ} (A : BananaMatrixStructure l r) where
  left : Submodule F2 (Fin l → F2)
  right : Submodule F2 (Fin r → F2)

/-- Fixed coordinate presentation for each actual two-sorted subpair. -/
noncomputable def BananaActualSubpair.presentation
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U : BananaActualSubpair A) : BananaPresentedSubpair A :=
  Classical.choose (A.exists_presentedSubpair_with_ranges U.left U.right)

theorem BananaActualSubpair.presentation_range_left
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U : BananaActualSubpair A) :
    LinearMap.range U.presentation.inclusion.left = U.left :=
  (Classical.choose_spec (A.exists_presentedSubpair_with_ranges U.left U.right)).1

theorem BananaActualSubpair.presentation_range_right
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U : BananaActualSubpair A) :
    LinearMap.range U.presentation.inclusion.right = U.right :=
  (Classical.choose_spec (A.exists_presentedSubpair_with_ranges U.left U.right)).2

/-- The left coordinate space identifies linearly with the actual left
subspace, not merely with an arbitrary subset of the ambient space. -/
noncomputable def BananaActualSubpair.leftCoordinateEquiv
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U : BananaActualSubpair A) :
    (Fin U.presentation.leftDim → F2) ≃ₗ[F2] U.left := by
  let e := U.presentation.inclusion.left
  have he (x) : e x ∈ U.left := by
    rw [← U.presentation_range_left]
    exact ⟨x, rfl⟩
  let f : (Fin U.presentation.leftDim → F2) →ₗ[F2] U.left :=
    e.codRestrict U.left he
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply U.presentation.inclusion.left_injective
      exact congrArg Subtype.val h
    · intro z
      have hz : (z : Fin l → F2) ∈ LinearMap.range e := by
        rw [U.presentation_range_left]
        exact z.property
      obtain ⟨x, hx⟩ := hz
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hx
  exact LinearEquiv.ofBijective f hf

/-- The corresponding right-side coordinate equivalence. -/
noncomputable def BananaActualSubpair.rightCoordinateEquiv
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U : BananaActualSubpair A) :
    (Fin U.presentation.rightDim → F2) ≃ₗ[F2] U.right := by
  let e := U.presentation.inclusion.right
  have he (y) : e y ∈ U.right := by
    rw [← U.presentation_range_right]
    exact ⟨y, rfl⟩
  let f : (Fin U.presentation.rightDim → F2) →ₗ[F2] U.right :=
    e.codRestrict U.right he
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply U.presentation.inclusion.right_injective
      exact congrArg Subtype.val h
    · intro z
      have hz : (z : Fin r → F2) ∈ LinearMap.range e := by
        rw [U.presentation_range_right]
        exact z.property
      obtain ⟨y, hy⟩ := hz
      refine ⟨y, ?_⟩
      apply Subtype.ext
      exact hy
  exact LinearEquiv.ofBijective f hf

/-- An actual partial automorphism between two actual substructures,
with the restricted bilinear pairing preserved on both sorts. -/
structure BananaActualSubpairIso
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U V : BananaActualSubpair A) where
  left : U.left ≃ₗ[F2] V.left
  right : U.right ≃ₗ[F2] V.right
  pairing_apply : ∀ x y,
    A.eval (left x).val (right y).val = A.eval x.val y.val

/-- Convert an original partial isomorphism into a pairing-preserving
matrix isomorphism of the once-chosen source and target presentations. -/
noncomputable def BananaActualSubpairIso.toPresentedIso
    {l r : ℕ} {A : BananaMatrixStructure l r}
    {U V : BananaActualSubpair A}
    (p : BananaActualSubpairIso U V) :
    BananaMatrixIso U.presentation.carrier V.presentation.carrier := by
  let f := (U.leftCoordinateEquiv.trans p.left).trans V.leftCoordinateEquiv.symm
  let g := (U.rightCoordinateEquiv.trans p.right).trans V.rightCoordinateEquiv.symm
  refine ⟨f, g, ?_⟩
  intro x y
  have hf : V.presentation.inclusion.left (f x) =
      ((p.left (U.leftCoordinateEquiv x) : V.left) : Fin l → F2) := by
    change ((V.leftCoordinateEquiv (V.leftCoordinateEquiv.symm
        (p.left (U.leftCoordinateEquiv x))) : V.left) : Fin l → F2) = _
    rw [LinearEquiv.apply_symm_apply]
  have hg : V.presentation.inclusion.right (g y) =
      ((p.right (U.rightCoordinateEquiv y) : V.right) : Fin r → F2) := by
    change ((V.rightCoordinateEquiv (V.rightCoordinateEquiv.symm
        (p.right (U.rightCoordinateEquiv y))) : V.right) : Fin r → F2) = _
    rw [LinearEquiv.apply_symm_apply]
  calc
    V.presentation.carrier.eval (f x) (g y) =
        A.eval (V.presentation.inclusion.left (f x))
          (V.presentation.inclusion.right (g y)) :=
      (V.presentation.inclusion.pairing_apply (f x) (g y)).symm
    _ = A.eval (p.left (U.leftCoordinateEquiv x)).val
          (p.right (U.rightCoordinateEquiv y)).val := by rw [hf, hg]
    _ = A.eval (U.leftCoordinateEquiv x).val
          (U.rightCoordinateEquiv y).val := p.pairing_apply _ _
    _ = A.eval (U.presentation.inclusion.left x)
          (U.presentation.inclusion.right y) := rfl
    _ = U.presentation.carrier.eval x y :=
      U.presentation.inclusion.pairing_apply x y

/-- The endpoints of every actual partial isomorphism have the same
isomorphism class of coordinate presentations. -/
theorem BananaActualSubpairIso.same_presented_class
    {l r : ℕ} {A : BananaMatrixStructure l r}
    {U V : BananaActualSubpair A}
    (p : BananaActualSubpairIso U V) :
    bananaPresentedClassOf U.presentation =
      bananaPresentedClassOf V.presentation :=
  bananaPresentedClassOf_eq_of_iso U.presentation V.presentation p.toPresentedIso

end SuccessorTree.NonPrecompact
