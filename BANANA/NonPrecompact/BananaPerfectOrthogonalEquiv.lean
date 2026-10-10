import BANANA.NonPrecompact.BananaPerfectOrthogonalDecomposition

/-!
# Splitting linear retractions into their range and kernel

For linear maps i : U → V and p : V → U with p ∘ i = id,
the addition map from U × ker p to V is a linear equivalence.
Both inverse components are canonical: project by p and take the
residual v - i(p v). No basis choice is necessary.

Specialising to the canonical pairing retractions of an embedded
finite perfect BANANA subpair gives the actual two-sorted
orthogonal direct-sum equivalences used in the ample-generics
amalgamation argument.
-/

namespace SuccessorTree.NonPrecompact

variable {U V : Type*}
variable [AddCommGroup U] [AddCommGroup V]
variable [Module F2 U] [Module F2 V]

/-- Every split linear retraction gives a canonical product–kernel
decomposition with the chosen section i. -/
noncomputable def bananaRetractionKernelEquiv
    (i : U →ₗ[F2] V) (p : V →ₗ[F2] U)
    (h : ∀ u, p (i u) = u) :
    (U × (LinearMap.ker p)) ≃ₗ[F2] V where
  toFun x := i x.1 + x.2.1
  invFun v :=
    (p v, ⟨v - i (p v), by
      change p (v - i (p v)) = 0
      simp [h]⟩)
  left_inv := by
    rintro ⟨u, z⟩
    have hz : p (z : V) = 0 := (LinearMap.mem_ker).mp z.property
    apply Prod.ext
    · change p (i u + (z : V)) = u
      simp [h, hz]
    · apply Subtype.ext
      change (i u + (z : V)) -
        i (p (i u + (z : V))) = (z : V)
      simp [h, hz]
  right_inv := by
    intro v
    change i (p v) + (v - i (p v)) = v
    abel
  map_add' := by
    rintro ⟨u, z⟩ ⟨u', z'⟩
    change i (u + u') + ((z : V) + (z' : V)) =
      (i u + (z : V)) + (i u' + (z' : V))
    rw [map_add]
    abel
  map_smul' := by
    intro c x
    change i (c • x.1) + c • (x.2 : V) =
      c • (i x.1 + (x.2 : V))
    rw [map_smul, smul_add]

/-- The canonical left orthogonal splitting of an arbitrary embedded
finite perfect BANANA subpair, as a genuine linear equivalence. -/
noncomputable def bananaPerfectLeftOrthogonalEquiv
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n)) :
    ((Fin m → F2) × (LinearMap.ker (rightPairingMap E))) ≃ₗ[F2]
      (Fin n → F2) :=
  bananaRetractionKernelEquiv E.left (rightPairingMap E)
    (rightPairingMap_left_retraction E)

/-- The canonical right orthogonal splitting, using the left-sort
pairing retraction. -/
noncomputable def bananaPerfectRightOrthogonalEquiv
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n)) :
    ((Fin m → F2) × (LinearMap.ker (perfectLeftPairingMap E))) ≃ₗ[F2]
      (Fin n → F2) :=
  bananaRetractionKernelEquiv E.right (perfectLeftPairingMap E)
    (perfectLeftPairingMap_right_retraction E)

end SuccessorTree.NonPrecompact
