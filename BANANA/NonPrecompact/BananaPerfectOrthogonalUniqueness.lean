import BANANA.NonPrecompact.BananaPerfectOrthogonalDecomposition

/-!
# Uniqueness of orthogonal decomposition around an embedded perfect pair

The canonical left/right pairing maps retract the embedded perfect
subpair. Each annihilator is exactly the kernel of the corresponding
retraction, and the decomposition into an image vector and an
annihilator vector is unique.

Combined with the preceding existence lemmas, these statements
establish the intrinsic two-sorted orthogonal direct-sum property
without choosing coordinate bases for the complement.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- Orthogonality to the embedded right sort is equivalent to
vanishing of the canonical left-sort retraction. -/
theorem perfectPair_left_annihilator_projection_zero
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (z : Fin n → F2)
    (hz : ∀ y : Fin m → F2, z ⬝ᵥ E.right y = 0) :
    rightPairingMap E z = 0 := by
  apply dotProduct_eq
  intro y
  calc
    rightPairingMap E z ⬝ᵥ y = z ⬝ᵥ E.right y :=
      (rightPairingMap_pairing E z y).symm
    _ = 0 := hz y
    _ = (0 : Fin m → F2) ⬝ᵥ y := by simp

/-- Orthogonality to the embedded left sort is equivalent to
vanishing of the canonical right-sort retraction. -/
theorem perfectPair_right_annihilator_projection_zero
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (z : Fin n → F2)
    (hz : ∀ x : Fin m → F2, E.left x ⬝ᵥ z = 0) :
    perfectLeftPairingMap E z = 0 := by
  apply dotProduct_eq
  intro x
  calc
    perfectLeftPairingMap E z ⬝ᵥ x =
        x ⬝ᵥ perfectLeftPairingMap E z := by
          rw [dotProduct_comm]
    _ = E.left x ⬝ᵥ z :=
      (perfectLeftPairingMap_pairing E x z).symm
    _ = 0 := hz x
    _ = (0 : Fin m → F2) ⬝ᵥ x := by simp

/-- The representation of an ambient left vector as an embedded
left vector plus a right-annihilating component is unique. -/
theorem perfectPair_left_orthogonal_decomposition_unique
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (a a' : Fin m → F2)
    (z z' : Fin n → F2)
    (hz : ∀ y, z ⬝ᵥ E.right y = 0)
    (hz' : ∀ y, z' ⬝ᵥ E.right y = 0)
    (h : E.left a + z = E.left a' + z') :
    a = a' ∧ z = z' := by
  have hz0 := perfectPair_left_annihilator_projection_zero E z hz
  have hz'0 := perfectPair_left_annihilator_projection_zero E z' hz'
  have ha : a = a' := by
    have hq := congrArg (rightPairingMap E) h
    simpa [map_add, rightPairingMap_left_retraction, hz0, hz'0] using hq
  refine ⟨ha, ?_⟩
  rw [ha] at h
  exact add_left_cancel h

/-- The analogous uniqueness of an ambient right vector's
embedded-plus-left-annihilating decomposition. -/
theorem perfectPair_right_orthogonal_decomposition_unique
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (b b' : Fin m → F2)
    (z z' : Fin n → F2)
    (hz : ∀ x, E.left x ⬝ᵥ z = 0)
    (hz' : ∀ x, E.left x ⬝ᵥ z' = 0)
    (h : E.right b + z = E.right b' + z') :
    b = b' ∧ z = z' := by
  have hz0 := perfectPair_right_annihilator_projection_zero E z hz
  have hz'0 := perfectPair_right_annihilator_projection_zero E z' hz'
  have hb : b = b' := by
    have hq := congrArg (perfectLeftPairingMap E) h
    simpa [map_add, perfectLeftPairingMap_right_retraction, hz0, hz'0] using hq
  refine ⟨hb, ?_⟩
  rw [hb] at h
  exact add_left_cancel h

end SuccessorTree.NonPrecompact
