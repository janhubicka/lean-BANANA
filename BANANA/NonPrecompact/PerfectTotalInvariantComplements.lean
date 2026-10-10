import BANANA.NonPrecompact.PerfectSelfEmbedding

/-!
# Invariance of orthogonal complements in perfect BANANA systems

Let A and B be finite perfect pairs. A total automorphism of B
preserving an embedded copy of A preserves the corresponding
orthogonal complements on both sorts. The proof uses only
pairing preservation, intertwining on the shared copy and
surjectivity of the source automorphisms.

This avoids choosing bases for the complements and is the
invariance step in the ample-generics amalgamation argument.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- Invariance of the left annihilator of the embedded right sort
under a pairing automorphism intertwining the source right action. -/
theorem perfectPair_leftAnnihilator_invariant
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (fR : (Fin m → F2) ≃ₗ[F2] (Fin m → F2))
    (hR : ∀ y, H.right (E.right y) = E.right (fR y))
    (x : Fin n → F2)
    (hx : ∀ y : Fin m → F2, x ⬝ᵥ E.right y = 0) :
    ∀ y : Fin m → F2, H.left x ⬝ᵥ E.right y = 0 := by
  intro y
  obtain ⟨z, rfl⟩ := fR.surjective y
  calc
    H.left x ⬝ᵥ E.right (fR z) =
        H.left x ⬝ᵥ H.right (E.right z) := by rw [hR z]
    _ = x ⬝ᵥ E.right z := by
      simpa only [perfectBanana_eval] using H.pairing_apply x (E.right z)
    _ = 0 := hx z

/-- Invariance of the right annihilator of the embedded left sort
under a pairing automorphism intertwining the source left action. -/
theorem perfectPair_rightAnnihilator_invariant
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (fL : (Fin m → F2) ≃ₗ[F2] (Fin m → F2))
    (hL : ∀ x, H.left (E.left x) = E.left (fL x))
    (y : Fin n → F2)
    (hy : ∀ x : Fin m → F2, E.left x ⬝ᵥ y = 0) :
    ∀ x : Fin m → F2, E.left x ⬝ᵥ H.right y = 0 := by
  intro x
  obtain ⟨z, rfl⟩ := fL.surjective x
  calc
    E.left (fL z) ⬝ᵥ H.right y =
        H.left (E.left z) ⬝ᵥ H.right y := by rw [hL z]
    _ = E.left z ⬝ᵥ y := by
      simpa only [perfectBanana_eval] using H.pairing_apply (E.left z) y
    _ = 0 := hy z

/-- The left-complement invariance assertion directly in terms
of two total perfect BANANA system automorphisms and their
intertwining embedded copy. -/
theorem perfectPair_leftAnnihilator_invariant_of_total
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (F : BananaMatrixEmbedding (perfectBanana m) (perfectBanana m))
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (hR : ∀ y, H.right (E.right y) = E.right (F.right y))
    (x : Fin n → F2)
    (hx : ∀ y : Fin m → F2, x ⬝ᵥ E.right y = 0) :
    ∀ y : Fin m → F2, H.left x ⬝ᵥ E.right y = 0 := by
  let fR : (Fin m → F2) ≃ₗ[F2] (Fin m → F2) :=
    LinearEquiv.ofBijective F.right
      ⟨F.right_injective,
        Finite.injective_iff_surjective.mp F.right_injective⟩
  exact perfectPair_leftAnnihilator_invariant E H fR hR x hx

/-- The corresponding right-complement invariance statement. -/
theorem perfectPair_rightAnnihilator_invariant_of_total
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (F : BananaMatrixEmbedding (perfectBanana m) (perfectBanana m))
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (hL : ∀ x, H.left (E.left x) = E.left (F.left x))
    (y : Fin n → F2)
    (hy : ∀ x : Fin m → F2, E.left x ⬝ᵥ y = 0) :
    ∀ x : Fin m → F2, E.left x ⬝ᵥ H.right y = 0 := by
  let fL : (Fin m → F2) ≃ₗ[F2] (Fin m → F2) :=
    F.leftSelfEquiv
  exact perfectPair_rightAnnihilator_invariant E H fL hL y hy

end SuccessorTree.NonPrecompact
