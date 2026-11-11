import BANANA.NonPrecompact.SymplecticAlternatingCoordinateTransport
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Pi

/-!
# Extending ordinary vector-space coordinates along injective maps

The age of finite alternating F₂-spaces includes degenerate forms.
Therefore the common subspace cannot in general be split off
orthogonally.  Instead, use the range of the embedding and an
ordinary vector-space complement.

This file constructs coordinates adapted to a given injection,
starting from arbitrary coordinates on the common source. It then
uses the SAME common coordinates for two different embeddings.
The resulting data are exactly the hypotheses of
symplecticAlternating_strongAmalgam_of_compatibleCoordinates.

All constructions are purely linear-algebraic. No nondegeneracy,
orthogonality or even bilinear form is assumed here. The next layer
combines these coordinates with the original alternating forms.

DRAFT / NOT KERNEL-VERIFIED: this code needs an exact-head local Lean
build and axiom audit before any manuscript validation marker.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

universe u

/-- Extend fixed coordinates on a source vector space along any
injective F₂-linear map.  The private complement gets its own finite
coordinate index.  Source vectors acquire zero private coordinates.

This is a vector-space, NOT orthogonal, complement construction. -/
theorem symplectic_exists_adapted_coordinates
    {VA VB A : Type u}
    [AddCommGroup VA] [Module F2 VA]
    [AddCommGroup VB] [Module F2 VB]
    [FiniteDimensional F2 VB]
    [Fintype A]
    (eA : VA ≃ₗ[F2] (A → F2))
    (i : VA →ₗ[F2] VB)
    (hi : Function.Injective i) :
    ∃ (X : Type u), ∃ (finX : Fintype X),
      ∃ eB : VB ≃ₗ[F2] (Sum A X → F2),
        ∀ a : VA,
          eB (i a) = symplecticBlockVectorCommonLeft (eA a) := by
  classical
  let p : Submodule F2 VB := LinearMap.range i
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl p
  let X : Type u := Basis.ofVectorSpaceIndex F2 q
  let bQ : Basis X F2 q := Basis.ofVectorSpace F2 q
  let finX : Fintype X := FiniteDimensional.fintypeBasisIndex bQ
  letI : Fintype X := finX
  let eQ : q ≃ₗ[F2] (X → F2) :=
    bQ.repr.trans (Finsupp.linearEquivFunOnFinite F2 F2 X)
  let eP : VA ≃ₗ[F2] p := LinearEquiv.ofInjective i hi
  let ePcoord : p ≃ₗ[F2] (A → F2) := eP.symm.trans eA
  let split : (p × q) ≃ₗ[F2] VB :=
    Submodule.prodEquivOfIsCompl p q hq
  let eB : VB ≃ₗ[F2] (Sum A X → F2) :=
    split.symm.trans
      ((LinearEquiv.prodCongr ePcoord eQ).trans
        (LinearEquiv.sumArrowLequivProdArrow A X F2 F2).symm)
  refine ⟨X, finX, eB, ?_⟩
  intro a
  have hsplit : split.symm (i a) = (eP a, (0 : q)) := by
    have h := Submodule.prodEquivOfIsCompl_symm_apply_left
      (p := p) (q := q) hq (eP a)
    simpa only [split, eP, LinearEquiv.ofInjective_apply] using h
  have hP : ePcoord (eP a) = eA a := by
    simp [ePcoord]
  change (LinearEquiv.sumArrowLequivProdArrow A X F2 F2).symm
    ((LinearEquiv.prodCongr ePcoord eQ) (split.symm (i a))) =
      symplecticBlockVectorCommonLeft (eA a)
  rw [hsplit]
  change (LinearEquiv.sumArrowLequivProdArrow A X F2 F2).symm
    (ePcoord (eP a), eQ (0 : q)) =
      symplecticBlockVectorCommonLeft (eA a)
  rw [hP, map_zero]
  funext k
  cases k with
  | inl j =>
      simp [symplecticBlockVectorCommonLeft]
  | inr j =>
      simp [symplecticBlockVectorCommonLeft]

/-- Two injections of the same source can be coordinatised with
exactly the SAME basis for that source, while each target receives
an independent ordinary vector-space complement.

This is the compatible-basis existence obligation of the symplectic
amalgamation proof, without additional bilinear hypotheses. -/
theorem symplectic_exists_compatible_coordinates
    {VA VB VC A : Type u}
    [AddCommGroup VA] [Module F2 VA]
    [AddCommGroup VB] [Module F2 VB]
    [AddCommGroup VC] [Module F2 VC]
    [FiniteDimensional F2 VB]
    [FiniteDimensional F2 VC]
    [Fintype A]
    (eA : VA ≃ₗ[F2] (A → F2))
    (iB : VA →ₗ[F2] VB) (iC : VA →ₗ[F2] VC)
    (hiB : Function.Injective iB)
    (hiC : Function.Injective iC) :
    ∃ (X Y : Type u), ∃ (finX : Fintype X) (finY : Fintype Y),
      ∃ (eB : VB ≃ₗ[F2] (Sum A X → F2))
        (eC : VC ≃ₗ[F2] (Sum A Y → F2)),
          (∀ a : VA,
            eB (iB a) = symplecticBlockVectorCommonLeft (eA a)) ∧
          (∀ a : VA,
            eC (iC a) = symplecticBlockVectorCommonRight (eA a)) := by
  classical
  obtain ⟨X, finX, eB, hB⟩ :=
    symplectic_exists_adapted_coordinates eA iB hiB
  obtain ⟨Y, finY, eC', hC⟩ :=
    symplectic_exists_adapted_coordinates eA iC hiC
  let eC : VC ≃ₗ[F2] (Sum A Y → F2) := eC'
  refine ⟨X, Y, finX, finY, eB, eC, hB, ?_⟩
  intro a
  -- Both common injections use the same source coordinates eA;
  -- the common-left and common-right zero-extensions coincide as functions.
  simpa [symplecticBlockVectorCommonLeft,
    symplecticBlockVectorCommonRight] using hC a


/-- A common basis and compatible complementary coordinates exist
for ANY two injective linear maps from the same finite-dimensional
F₂-source, including zero-dimensional and degenerate cases.

The index sets of the private summands may differ. This theorem
does not refer to a bilinear form: pairing compatibility is a
separate consequence of the assumed isometry equations. -/
theorem symplectic_exists_common_adapted_coordinates
    {VA VB VC : Type u}
    [AddCommGroup VA] [Module F2 VA]
    [AddCommGroup VB] [Module F2 VB]
    [AddCommGroup VC] [Module F2 VC]
    [FiniteDimensional F2 VA]
    [FiniteDimensional F2 VB]
    [FiniteDimensional F2 VC]
    (iB : VA →ₗ[F2] VB) (iC : VA →ₗ[F2] VC)
    (hiB : Function.Injective iB)
    (hiC : Function.Injective iC) :
    ∃ (A X Y : Type u),
      ∃ (finA : Fintype A) (finX : Fintype X) (finY : Fintype Y),
        ∃ (eA : VA ≃ₗ[F2] (A → F2))
          (eB : VB ≃ₗ[F2] (Sum A X → F2))
          (eC : VC ≃ₗ[F2] (Sum A Y → F2)),
          (∀ a : VA,
            eB (iB a) = symplecticBlockVectorCommonLeft (eA a)) ∧
          (∀ a : VA,
            eC (iC a) = symplecticBlockVectorCommonRight (eA a)) := by
  classical
  let A : Type u := Basis.ofVectorSpaceIndex F2 VA
  let bA : Basis A F2 VA := Basis.ofVectorSpace F2 VA
  let finA : Fintype A := FiniteDimensional.fintypeBasisIndex bA
  letI : Fintype A := finA
  let eA : VA ≃ₗ[F2] (A → F2) :=
    bA.repr.trans (Finsupp.linearEquivFunOnFinite F2 F2 A)
  obtain ⟨X, Y, finX, finY, eB, eC, hB, hC⟩ :=
    symplectic_exists_compatible_coordinates eA iB iC hiB hiC
  exact ⟨A, X, Y, finA, finX, finY, eA, eB, eC, hB, hC⟩

end SuccessorTree.NonPrecompact
