import BANANA.NonPrecompact.BananaPerfectOrthogonalNondegenerate

/-!
# The induced perfect bilinear pairing on orthogonal complements

For an embedding of finite perfect BANANA pairings, restrict the
ambient dot product to the left and right annihilator kernels.
This yields a bilinear map between finite vector spaces which
is nondegenerate on both sorts.

These are the abstract complementary perfect pairings B₀,C₀
in the circulation proof of ample generics; no bases are chosen.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- The ambient dot product, restricted bilinearly to the two
orthogonal complements of an embedded perfect subpair. -/
noncomputable def perfectComplementPairing
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n)) :
    (LinearMap.ker (rightPairingMap E)) →ₗ[F2]
      ((LinearMap.ker (perfectLeftPairingMap E)) →ₗ[F2] F2) where
  toFun x := {
    toFun := fun y => (x : Fin n → F2) ⬝ᵥ (y : Fin n → F2)
    map_add' := by
      intro y z
      change (x : Fin n → F2) ⬝ᵥ
          ((y : Fin n → F2) + (z : Fin n → F2)) =
        (x : Fin n → F2) ⬝ᵥ (y : Fin n → F2) +
        (x : Fin n → F2) ⬝ᵥ (z : Fin n → F2)
      rw [dotProduct_add]
    map_smul' := by
      intro c y
      change (x : Fin n → F2) ⬝ᵥ (c • (y : Fin n → F2)) =
        c • ((x : Fin n → F2) ⬝ᵥ (y : Fin n → F2))
      exact dotProduct_smul c _ _
  }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change ((x : Fin n → F2) + (y : Fin n → F2)) ⬝ᵥ
        (z : Fin n → F2) =
      (x : Fin n → F2) ⬝ᵥ (z : Fin n → F2) +
      (y : Fin n → F2) ⬝ᵥ (z : Fin n → F2)
    rw [add_dotProduct]
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro z
    change (c • (x : Fin n → F2)) ⬝ᵥ (z : Fin n → F2) =
      c • ((x : Fin n → F2) ⬝ᵥ (z : Fin n → F2))
    exact smul_dotProduct c _ _

/-- The restricted pairing evaluates to the ambient dot product. -/
theorem perfectComplementPairing_apply
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (x : LinearMap.ker (rightPairingMap E))
    (y : LinearMap.ker (perfectLeftPairingMap E)) :
    perfectComplementPairing E x y =
      (x : Fin n → F2) ⬝ᵥ (y : Fin n → F2) := rfl

/-- The complementary pairing is nondegenerate on the left. -/
theorem perfectComplementPairing_left_nondegenerate
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (x : LinearMap.ker (rightPairingMap E))
    (hx : ∀ y : LinearMap.ker (perfectLeftPairingMap E),
      perfectComplementPairing E x y = 0) :
    x = 0 := by
  have hA : ∀ b : Fin m → F2,
      (x : Fin n → F2) ⬝ᵥ E.right b = 0 := by
    intro b
    have hz : rightPairingMap E (x : Fin n → F2) = 0 :=
      (LinearMap.mem_ker).mp x.property
    have hp := rightPairingMap_pairing E (x : Fin n → F2) b
    simpa [hz] using hp
  have hK : ∀ z : Fin n → F2,
      (∀ a : Fin m → F2, E.left a ⬝ᵥ z = 0) →
      (x : Fin n → F2) ⬝ᵥ z = 0 := by
    intro z hz
    have hright : perfectLeftPairingMap E z = 0 := by
      apply dotProduct_eq
      intro a
      calc
        perfectLeftPairingMap E z ⬝ᵥ a =
            a ⬝ᵥ perfectLeftPairingMap E z := by rw [dotProduct_comm]
        _ = E.left a ⬝ᵥ z :=
          (perfectLeftPairingMap_pairing E a z).symm
        _ = 0 := hz a
        _ = (0 : Fin m → F2) ⬝ᵥ a := by simp
    have hz' : z ∈ LinearMap.ker (perfectLeftPairingMap E) :=
      (LinearMap.mem_ker).mpr hright
    exact hx ⟨z, hz'⟩
  apply Subtype.ext
  exact perfectPair_leftComplement_nondegenerate E
    (x : Fin n → F2) hA hK

/-- The complementary pairing is nondegenerate on the right. -/
theorem perfectComplementPairing_right_nondegenerate
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (y : LinearMap.ker (perfectLeftPairingMap E))
    (hy : ∀ x : LinearMap.ker (rightPairingMap E),
      perfectComplementPairing E x y = 0) :
    y = 0 := by
  have hA : ∀ a : Fin m → F2,
      E.left a ⬝ᵥ (y : Fin n → F2) = 0 := by
    intro a
    have hz : perfectLeftPairingMap E (y : Fin n → F2) = 0 :=
      (LinearMap.mem_ker).mp y.property
    have hp := perfectLeftPairingMap_pairing E a (y : Fin n → F2)
    simpa [hz] using hp
  have hK : ∀ z : Fin n → F2,
      (∀ b : Fin m → F2, z ⬝ᵥ E.right b = 0) →
      z ⬝ᵥ (y : Fin n → F2) = 0 := by
    intro z hz
    have hleft : rightPairingMap E z = 0 := by
      apply dotProduct_eq
      intro b
      calc
        rightPairingMap E z ⬝ᵥ b = z ⬝ᵥ E.right b :=
          (rightPairingMap_pairing E z b).symm
        _ = 0 := hz b
        _ = (0 : Fin m → F2) ⬝ᵥ b := by simp
    have hz' : z ∈ LinearMap.ker (rightPairingMap E) :=
      (LinearMap.mem_ker).mpr hleft
    exact hy ⟨z, hz'⟩
  apply Subtype.ext
  exact perfectPair_rightComplement_nondegenerate E
    (y : Fin n → F2) hA hK

end SuccessorTree.NonPrecompact
