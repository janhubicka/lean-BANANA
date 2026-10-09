import BANANA.NonPrecompact.BananaLimitBlockProjection
import BANANA.NonPrecompact.BananaRetractionLiftEquiv

/-!
# Extending finite-block pairing automorphisms to the explicit BANANA limit

A pair of linear equivalences of one finite rational-coordinate block
preserving its bilinear pairing extends to an automorphism of the
two-sorted pairing on finitely supported vectors. The extension acts
as the identity on the coordinates outside that finite block.

This is a genuine finite-block extension statement, not yet the
ultrahomogeneity theorem: extending arbitrary isomorphisms between
finite *substructures* requires a further finite-dimensional lemma.
-/

namespace SuccessorTree.NonPrecompact

/-- Extend a linear automorphism of the S-supported block by the
identity on all coordinates outside S. -/
noncomputable def bananaLimitBlockLift
    (S : Finset ℚ)
    (e : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S) :
    BananaLimitVector ≃ₗ[F2] BananaLimitVector :=
  bananaRetractionLiftEquiv
    (U := bananaLimitBlock S) (V := BananaLimitVector)
    (bananaLimitBlock S).subtype (bananaLimitFinitePart S)
    (bananaLimitFinitePart_on_block S) e

/-- The lifted map restricts to the given finite-block map. -/
theorem bananaLimitBlockLift_on_block
    (S : Finset ℚ)
    (e : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S)
    (u : bananaLimitBlock S) :
    bananaLimitBlockLift S e (u : BananaLimitVector) =
      (e u : BananaLimitVector) := by
  simpa only [bananaLimitBlockLift, Submodule.subtype_apply] using
    (bananaRetractionLiftEquiv_on_range
      (U := bananaLimitBlock S) (V := BananaLimitVector)
      (bananaLimitBlock S).subtype (bananaLimitFinitePart S)
      (bananaLimitFinitePart_on_block S) e u)

/-- The lifted map fixes the outside-coordinate component. -/
theorem bananaLimitBlockLift_on_outside
    (S : Finset ℚ)
    (e : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S)
    (x : BananaLimitVector) :
    bananaLimitBlockLift S e (bananaLimitOutsidePart S x) =
      bananaLimitOutsidePart S x := by
  have h :=
    bananaRetractionLiftLinear_on_ker
      (U := bananaLimitBlock S) (V := BananaLimitVector)
      (bananaLimitBlock S).subtype (bananaLimitFinitePart S)
      e.toLinearMap (bananaLimitOutsidePart S x)
      (bananaLimitFinitePart_outside_zero S x)
  change bananaRetractionLiftLinear
      (U := bananaLimitBlock S) (V := BananaLimitVector)
      (bananaLimitBlock S).subtype (bananaLimitFinitePart S)
      e.toLinearMap (bananaLimitOutsidePart S x) =
    bananaLimitOutsidePart S x
  exact h

/-- The lifted map acts on the inside part, leaving the outside part
untouched. This follows from the direct-sum decomposition. -/
theorem bananaLimitBlockLift_apply
    (S : Finset ℚ)
    (e : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S)
    (x : BananaLimitVector) :
    bananaLimitBlockLift S e x =
      (e (bananaLimitFinitePart S x) : BananaLimitVector) +
        bananaLimitOutsidePart S x := by
  calc
    bananaLimitBlockLift S e x =
        bananaLimitBlockLift S e
          ((bananaLimitFinitePart S x : BananaLimitVector) +
            bananaLimitOutsidePart S x) := by
          rw [bananaLimit_finite_outside_decomposition S x]
    _ = bananaLimitBlockLift S e
          (bananaLimitFinitePart S x : BananaLimitVector) +
          bananaLimitBlockLift S e (bananaLimitOutsidePart S x) := by
          rw [map_add]
    _ = (e (bananaLimitFinitePart S x) : BananaLimitVector) +
          bananaLimitOutsidePart S x := by
          rw [bananaLimitBlockLift_on_block, bananaLimitBlockLift_on_outside]

/-- Every block-supported vector is orthogonal, in the reverse sort
order, to the outside part of an arbitrary vector. -/
theorem bananaLimitPairing_block_outside_zero
    (S : Finset ℚ) (u : bananaLimitBlock S)
    (y : BananaLimitVector) :
    bananaLimitPairing (u : BananaLimitVector)
      (bananaLimitOutsidePart S y) = 0 := by
  apply bananaLimitPairing_eq_zero_of_disjoint_support
  apply Finset.disjoint_left.mpr
  intro q hqu hqy
  have hqS : q ∈ S :=
    ((bananaLimitBlock_mem_iff S (u : BananaLimitVector)).mp
      u.property) hqu
  have hz : (bananaLimitOutsidePart S y) q = 0 :=
    bananaLimitOutsidePart_apply_mem S y q hqS
  exact (Finsupp.mem_support_iff.mp hqy) hz

/-- The pairing splits into the finite-block pairing plus the
pairing of outside-coordinate components, with no mixed terms. -/
theorem bananaLimitPairing_finite_outside_split
    (S : Finset ℚ) (x y : BananaLimitVector) :
    bananaLimitPairing x y =
      bananaLimitPairing
        (bananaLimitFinitePart S x : BananaLimitVector)
        (bananaLimitFinitePart S y : BananaLimitVector) +
      bananaLimitPairing
        (bananaLimitOutsidePart S x)
        (bananaLimitOutsidePart S y) := by
  have hLR :
      bananaLimitPairing (bananaLimitFinitePart S x : BananaLimitVector)
        (bananaLimitOutsidePart S y) = 0 :=
    bananaLimitPairing_block_outside_zero S
      (bananaLimitFinitePart S x) y
  have hRL :
      bananaLimitPairing (bananaLimitOutsidePart S x)
        (bananaLimitFinitePart S y : BananaLimitVector) = 0 :=
    bananaLimitPairing_outside_block_zero S x
      (bananaLimitFinitePart S y)
  calc
    bananaLimitPairing x y =
        bananaLimitPairing
          ((bananaLimitFinitePart S x : BananaLimitVector) +
            bananaLimitOutsidePart S x)
          ((bananaLimitFinitePart S y : BananaLimitVector) +
            bananaLimitOutsidePart S y) := by
          rw [bananaLimit_finite_outside_decomposition S x,
            bananaLimit_finite_outside_decomposition S y]
    _ = bananaLimitPairing
          (bananaLimitFinitePart S x : BananaLimitVector)
          (bananaLimitFinitePart S y : BananaLimitVector) +
        bananaLimitPairing
          (bananaLimitOutsidePart S x)
          (bananaLimitOutsidePart S y) := by
          rw [bananaLimitPairing_add_left,
            bananaLimitPairing_add_right,
            bananaLimitPairing_add_right, hLR, hRL]
          abel

/-- Pairing-preserving maps of a common finite block lift to
pairing-preserving linear automorphisms of the full limit. -/
theorem bananaLimitBlockLift_pairing
    (S : Finset ℚ)
    (eL eR : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S)
    (hpair : ∀ u v : bananaLimitBlock S,
      bananaLimitPairing (eL u : BananaLimitVector)
        (eR v : BananaLimitVector) =
      bananaLimitPairing (u : BananaLimitVector)
        (v : BananaLimitVector))
    (x y : BananaLimitVector) :
    bananaLimitPairing
      (bananaLimitBlockLift S eL x)
      (bananaLimitBlockLift S eR y) =
    bananaLimitPairing x y := by
  have hLR :
      bananaLimitPairing
        (eL (bananaLimitFinitePart S x) : BananaLimitVector)
        (bananaLimitOutsidePart S y) = 0 :=
    bananaLimitPairing_block_outside_zero S
      (eL (bananaLimitFinitePart S x)) y
  have hRL :
      bananaLimitPairing (bananaLimitOutsidePart S x)
        (eR (bananaLimitFinitePart S y) : BananaLimitVector) = 0 :=
    bananaLimitPairing_outside_block_zero S x
      (eR (bananaLimitFinitePart S y))
  calc
    bananaLimitPairing
        (bananaLimitBlockLift S eL x)
        (bananaLimitBlockLift S eR y) =
      bananaLimitPairing
        (eL (bananaLimitFinitePart S x) : BananaLimitVector)
        (eR (bananaLimitFinitePart S y) : BananaLimitVector) +
      bananaLimitPairing
        (bananaLimitOutsidePart S x)
        (bananaLimitOutsidePart S y) := by
        rw [bananaLimitBlockLift_apply, bananaLimitBlockLift_apply,
          bananaLimitPairing_add_left, bananaLimitPairing_add_right,
          bananaLimitPairing_add_right, hLR, hRL]
        abel
    _ = bananaLimitPairing
          (bananaLimitFinitePart S x : BananaLimitVector)
          (bananaLimitFinitePart S y : BananaLimitVector) +
        bananaLimitPairing
          (bananaLimitOutsidePart S x)
          (bananaLimitOutsidePart S y) := by
        rw [hpair (bananaLimitFinitePart S x)
          (bananaLimitFinitePart S y)]
    _ = bananaLimitPairing x y :=
      (bananaLimitPairing_finite_outside_split S x y).symm

/-- A pairing automorphism of one finite perfect coordinate block
extends to an automorphism of the entire two-sorted BANANA pairing.
Both sorts are allowed different linear equivalences. -/
theorem exists_bananaLimit_global_pair_automorphism_of_block
    (S : Finset ℚ)
    (eL eR : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S)
    (hpair : ∀ u v : bananaLimitBlock S,
      bananaLimitPairing (eL u : BananaLimitVector)
        (eR v : BananaLimitVector) =
      bananaLimitPairing (u : BananaLimitVector)
        (v : BananaLimitVector)) :
    ∃ EL ER : BananaLimitVector ≃ₗ[F2] BananaLimitVector,
      (∀ x y : BananaLimitVector,
        bananaLimitPairing (EL x) (ER y) =
          bananaLimitPairing x y) ∧
      (∀ u : bananaLimitBlock S,
        EL (u : BananaLimitVector) = (eL u : BananaLimitVector)) ∧
      (∀ v : bananaLimitBlock S,
        ER (v : BananaLimitVector) = (eR v : BananaLimitVector)) := by
  refine ⟨bananaLimitBlockLift S eL, bananaLimitBlockLift S eR,
    ?_, ?_, ?_⟩
  · exact bananaLimitBlockLift_pairing S eL eR hpair
  · exact bananaLimitBlockLift_on_block S eL
  · exact bananaLimitBlockLift_on_block S eR

end SuccessorTree.NonPrecompact
