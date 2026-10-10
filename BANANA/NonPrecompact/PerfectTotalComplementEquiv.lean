import BANANA.NonPrecompact.PerfectTotalInvariantComplements
import BANANA.NonPrecompact.BananaPerfectOrthogonalDecomposition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Automorphisms induced on the invariant orthogonal complements

If a perfect-total BANANA automorphism H of B_n intertwines
the self-automorphism F of a perfect embedded B_m, H preserves
the two annihilators of the embedded pair. Its restrictions to the
annihilators are automatically linear equivalences (finite-dimensional
injectivity implies surjectivity).

The two induced equivalences also preserve the bilinear pairing
on the complementary subspaces. This is the coordinate-free
complement-action input in the ample-generics amalgamation argument.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- Restriction of the ambient left action to the annihilator of
the embedded right sort. -/
noncomputable def perfectTotalLeftComplementEquiv
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (F : BananaMatrixEmbedding (perfectBanana m) (perfectBanana m))
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (hR : ∀ y, H.right (E.right y) = E.right (F.right y)) :
    LinearMap.ker (rightPairingMap E) ≃ₗ[F2]
      LinearMap.ker (rightPairingMap E) := by
  classical
  let W := LinearMap.ker (rightPairingMap E)
  let f : W →ₗ[F2] W :=
    (H.left.domRestrict W).codRestrict W (by
      intro w
      have hw : ∀ y : Fin m → F2,
          (w : Fin n → F2) ⬝ᵥ E.right y = 0 := by
        intro y
        have hzero : rightPairingMap E (w : Fin n → F2) = 0 :=
          (LinearMap.mem_ker).mp w.property
        have hp := rightPairingMap_pairing E (w : Fin n → F2) y
        simpa [hzero] using hp
      have hInv :=
        perfectPair_leftAnnihilator_invariant_of_total
          E F H hR (w : Fin n → F2) hw
      apply (LinearMap.mem_ker).mpr
      apply dotProduct_eq
      intro y
      calc
        rightPairingMap E (H.left (w : Fin n → F2)) ⬝ᵥ y =
            H.left (w : Fin n → F2) ⬝ᵥ E.right y :=
          (rightPairingMap_pairing E _ y).symm
        _ = 0 := hInv y
        _ = (0 : Fin m → F2) ⬝ᵥ y := by simp)
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply H.left_injective
    simpa only [f, LinearMap.codRestrict_apply,
      LinearMap.domRestrict_apply] using congrArg Subtype.val h
  exact LinearEquiv.ofBijective f
    ⟨hi, Finite.injective_iff_surjective.mp hi⟩

/-- Restriction of the ambient right action to the annihilator
of the embedded left sort. -/
noncomputable def perfectTotalRightComplementEquiv
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (F : BananaMatrixEmbedding (perfectBanana m) (perfectBanana m))
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (hL : ∀ x, H.left (E.left x) = E.left (F.left x)) :
    LinearMap.ker (perfectLeftPairingMap E) ≃ₗ[F2]
      LinearMap.ker (perfectLeftPairingMap E) := by
  classical
  let W := LinearMap.ker (perfectLeftPairingMap E)
  let f : W →ₗ[F2] W :=
    (H.right.domRestrict W).codRestrict W (by
      intro w
      have hw : ∀ x : Fin m → F2,
          E.left x ⬝ᵥ (w : Fin n → F2) = 0 := by
        intro x
        have hzero :
            perfectLeftPairingMap E (w : Fin n → F2) = 0 :=
          (LinearMap.mem_ker).mp w.property
        have hp := perfectLeftPairingMap_pairing
          E x (w : Fin n → F2)
        simpa [hzero] using hp
      have hInv :=
        perfectPair_rightAnnihilator_invariant_of_total
          E F H hL (w : Fin n → F2) hw
      apply (LinearMap.mem_ker).mpr
      apply dotProduct_eq
      intro x
      calc
        perfectLeftPairingMap E (H.right (w : Fin n → F2)) ⬝ᵥ x =
            x ⬝ᵥ perfectLeftPairingMap E (H.right (w : Fin n → F2)) := by
              rw [dotProduct_comm]
        _ = E.left x ⬝ᵥ H.right (w : Fin n → F2) :=
          (perfectLeftPairingMap_pairing E x _).symm
        _ = 0 := hInv x
        _ = (0 : Fin m → F2) ⬝ᵥ x := by simp)
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply H.right_injective
    simpa only [f, LinearMap.codRestrict_apply,
      LinearMap.domRestrict_apply] using congrArg Subtype.val h
  exact LinearEquiv.ofBijective f
    ⟨hi, Finite.injective_iff_surjective.mp hi⟩

/-- The induced left/right complementary automorphisms preserve
the pairing restricted to the orthogonal complements. -/
theorem perfectTotalComplementEquivs_pairing
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (F : BananaMatrixEmbedding (perfectBanana m) (perfectBanana m))
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (hL : ∀ x, H.left (E.left x) = E.left (F.left x))
    (hR : ∀ y, H.right (E.right y) = E.right (F.right y))
    (x : LinearMap.ker (rightPairingMap E))
    (y : LinearMap.ker (perfectLeftPairingMap E)) :
    (perfectTotalLeftComplementEquiv E F H hR x : Fin n → F2) ⬝ᵥ
        (perfectTotalRightComplementEquiv E F H hL y : Fin n → F2) =
      (x : Fin n → F2) ⬝ᵥ (y : Fin n → F2) := by
  have hLx :
      (perfectTotalLeftComplementEquiv E F H hR x : Fin n → F2) =
        H.left (x : Fin n → F2) := by
    rfl
  have hRy :
      (perfectTotalRightComplementEquiv E F H hL y : Fin n → F2) =
        H.right (y : Fin n → F2) := by
    rfl
  rw [hLx, hRy]
  simpa only [perfectBanana_eval] using
    H.pairing_apply (x : Fin n → F2) (y : Fin n → F2)

end SuccessorTree.NonPrecompact
