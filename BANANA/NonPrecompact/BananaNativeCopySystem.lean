import BANANA.NonPrecompact.BananaCopyDegree
import Mathlib.Algebra.Module.Submodule.Equiv
import BANANA.CopyRamsey

/-!
# The native BANANA copy system

Finite BANANA structures carry their usual coordinate matrices. The maps
are the genuine pairing-preserving embeddings, and copies are exactly
their pairs of image subspaces. A copy inside another copy factors through
its defining embedding. This realises the paper's copy degree in the
shared `FiniteCopySystem` interface.

The obstruction uses the shared `RamseyExpansion` interface for finite
expansion types, functorial hereditary restrictions and the embedding
Ramsey property.
-/

namespace SuccessorTree.NonPrecompact

private theorem factor_linearMap
    {V W U : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]
    [Module F2 V] [Module F2 W] [Module F2 U]
    (f : V →ₗ[F2] U) (g : W →ₗ[F2] U)
    (hg : Function.Injective g) (h : LinearMap.range f ≤ LinearMap.range g) :
    ∃ e : V →ₗ[F2] W, ∀ x, g (e x) = f x := by
  let gEquiv := LinearEquiv.ofInjective g hg
  let fRange := f.codRestrict (LinearMap.range g) fun x => h ⟨x, rfl⟩
  refine ⟨gEquiv.symm.toLinearMap.comp fRange, fun x => ?_⟩
  change (gEquiv (gEquiv.symm (fRange x))).val = f x
  rw [LinearEquiv.apply_symm_apply]
  rfl

namespace BananaMatrixEmbedding

private theorem ext_maps
    {l r lB rB : ℕ} {A : BananaMatrixStructure l r} {B : BananaMatrixStructure lB rB}
    {f g : BananaMatrixEmbedding A B}
    (hl : f.left = g.left) (hr : f.right = g.right) : f = g := by
  cases f
  cases g
  cases hl
  cases hr
  rfl

/-- An embedding whose two ranges lie in the ranges of a second embedding
factors through that second embedding. -/
theorem exists_factor_of_range_le
    {l r lB rB lC rC : ℕ} {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure lB rB} {C : BananaMatrixStructure lC rC}
    (f : BananaMatrixEmbedding A C) (g : BananaMatrixEmbedding B C)
    (hL : LinearMap.range f.left ≤ LinearMap.range g.left)
    (hR : LinearMap.range f.right ≤ LinearMap.range g.right) :
    ∃ e : BananaMatrixEmbedding A B, g.comp e = f := by
  obtain ⟨eL, heL⟩ := factor_linearMap f.left g.left g.left_injective hL
  obtain ⟨eR, heR⟩ := factor_linearMap f.right g.right g.right_injective hR
  let e : BananaMatrixEmbedding A B :=
    { left := eL
      right := eR
      left_injective := fun x y h =>
        f.left_injective ((heL x).symm.trans ((congrArg g.left h).trans (heL y)))
      right_injective := fun x y h =>
        f.right_injective ((heR x).symm.trans ((congrArg g.right h).trans (heR y)))
      pairing_apply := fun x y => by
        rw [← g.pairing_apply, heL, heR, f.pairing_apply] }
  exact ⟨e, ext_maps (LinearMap.ext heL) (LinearMap.ext heR)⟩

private def copySystemIdentity {l r : ℕ} (A : BananaMatrixStructure l r) :
    BananaMatrixEmbedding A A where
  left := LinearMap.id
  right := LinearMap.id
  left_injective := Function.injective_id
  right_injective := Function.injective_id
  pairing_apply _ _ := rfl

end BananaMatrixEmbedding

/-- A finite matrix presentation with both dimensions bundled. -/
structure BananaFiniteCopyObject where
  leftDim : ℕ
  rightDim : ℕ
  matrix : BananaMatrixStructure leftDim rightDim

/-- The pair of image subspaces gives the genuine native copy system. -/
noncomputable def bananaCopySystem : FiniteCopySystem := by
  classical
  exact
    { Obj := BananaFiniteCopyObject
      Emb := fun A B => BananaMatrixEmbedding A.matrix B.matrix
      Copy := fun A B => BananaCopyRanges A.matrix B.matrix
      idEmb := fun A => BananaMatrixEmbedding.copySystemIdentity A.matrix
      compEmb := fun f g => g.comp f
      comp_id_left := fun _ => BananaMatrixEmbedding.ext_maps rfl rfl
      comp_id_right := fun _ => BananaMatrixEmbedding.ext_maps rfl rfl
      comp_assoc := fun _ _ _ => BananaMatrixEmbedding.ext_maps rfl rfl
      range := BananaMatrixEmbedding.copyRanges
      mapCopy := fun f p => p.map f
      mapCopy_id := fun p => by
        apply Subtype.ext
        exact Prod.ext Finset.image_id Finset.image_id
      mapCopy_comp := fun f g p => by
        apply Subtype.ext
        apply Prod.ext
        · change p.val.1.image (g.left.comp f.left) = (p.val.1.image f.left).image g.left
          rw [Finset.image_image]
          rfl
        · change p.val.2.image (g.right.comp f.right) = (p.val.2.image f.right).image g.right
          rw [Finset.image_image]
          rfl
      range_comp := fun f g => (f.copyRanges_comp g).symm
      range_surjective := fun p => by
        obtain ⟨f, hL, hR⟩ := p.property
        exact ⟨f, Subtype.ext (Prod.ext hL.symm hR.symm)⟩
      Subcopy := fun p q => p.1.1 ⊆ q.1.1 ∧ p.1.2 ⊆ q.1.2
      subcopy_range_iff := fun f p => by
        constructor
        · rintro ⟨hL, hR⟩
          obtain ⟨g, hgL, hgR⟩ := p.property
          have hleft : LinearMap.range g.left ≤ LinearMap.range f.left := by
            rintro _ ⟨x, rfl⟩
            have hmem : g.left x ∈ p.val.1 := by
              rw [hgL]
              exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
            obtain ⟨y, _, hy⟩ := Finset.mem_image.mp (hL hmem)
            exact ⟨y, hy⟩
          have hright : LinearMap.range g.right ≤ LinearMap.range f.right := by
            rintro _ ⟨x, rfl⟩
            have hmem : g.right x ∈ p.val.2 := by
              rw [hgR]
              exact Finset.mem_image_of_mem _ (Finset.mem_univ x)
            obtain ⟨y, _, hy⟩ := Finset.mem_image.mp (hR hmem)
            exact ⟨y, hy⟩
          obtain ⟨e, he⟩ := g.exists_factor_of_range_le f hleft hright
          refine ⟨e.copyRanges, (e.copyRanges_comp f).trans ?_⟩
          rw [he]
          exact Subtype.ext (Prod.ext hgL.symm hgR.symm)
        · rintro ⟨q, rfl⟩
          exact ⟨Finset.image_subset_image (Finset.subset_univ _),
            Finset.image_subset_image (Finset.subset_univ _)⟩
      copyFintype := fun A B => bananaCopyRangesFintype A.matrix B.matrix
      copyDecidableEq := fun _ _ => Classical.decEq _ }

/-- The native BANANA degree and its packaged finite-copy-system degree
use the same unlabelled ranges. -/
theorem bananaCopySystem_copyRamseyDegreeLE_iff (A : BananaFiniteCopyObject) (d : ℕ) :
    bananaCopySystem.CopyRamseyDegreeLE A d ↔ A.matrix.copyRamseyDegreeLE d := by
  classical
  constructor
  · intro h lB rB B r hr
    obtain ⟨C, hC⟩ := h ⟨lB, rB, B⟩ r hr
    refine ⟨C.leftDim, C.rightDim, C.matrix, fun c => ?_⟩
    obtain ⟨f, hf⟩ := hC c
    refine ⟨f, bananaCopySystem.coloursInside c f, hf, fun p => ?_⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_univ p)
  · intro h B r hr
    obtain ⟨lC, rC, C, hC⟩ := h B.leftDim B.rightDim B.matrix r hr
    refine ⟨⟨lC, rC, C⟩, fun c => ?_⟩
    obtain ⟨f, colours, hc, hcolours⟩ := hC c
    refine ⟨f, (Finset.card_le_card ?_).trans hc⟩
    rintro _ hy
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hy
    exact hcolours p

/-- BANANA admits no hereditary precompact Ramsey expansion in the shared
expansion interface. -/
theorem banana_noPrecompactRamseyExpansion :
    ¬ Nonempty (RamseyExpansion bananaCopySystem) := by
  rintro ⟨E⟩
  let A : BananaFiniteCopyObject := ⟨1, 1, linePairSource 0⟩
  have hDegree := E.copyRamseyDegreeLE_card_expansionTypes A
  exact A.matrix.copyRamseyDegree_infinite_of_positive (by decide) (by decide) _
    ((bananaCopySystem_copyRamseyDegreeLE_iff A _).mp hDegree)

end SuccessorTree.NonPrecompact
