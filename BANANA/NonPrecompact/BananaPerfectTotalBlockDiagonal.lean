import BANANA.NonPrecompact.BananaPerfectOrthogonalEquiv
import BANANA.NonPrecompact.PerfectTotalComplementEquiv

/-!
# Perfect-total automorphisms become block diagonal under orthogonal splitting

For an embedded perfect subsystem E:B_m↪B_n, the canonical
linear equivalences identify the ambient left and right vector
spaces with products of the source and its annihilator. If H is
an ambient automorphism intertwining a source automorphism F,
these identifications carry H to the componentwise action of
F and the induced automorphism of the orthogonal complement.

Both sorts are treated separately, with the pairing preserved by
the complement maps. This is the basis-free conjugation interface
needed to reduce arbitrary perfect-total systems to split systems.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- The ambient left automorphism is block diagonal in the canonical
left image-plus-annihilator decomposition. -/
theorem perfectTotal_left_orthogonal_block_diagonal
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (F : BananaMatrixEmbedding (perfectBanana m) (perfectBanana m))
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (hL : ∀ a, H.left (E.left a) = E.left (F.left a))
    (hR : ∀ b, H.right (E.right b) = E.right (F.right b))
    (x : (Fin m → F2) ×
      (LinearMap.ker (rightPairingMap E))) :
    H.left (bananaPerfectLeftOrthogonalEquiv E x) =
      bananaPerfectLeftOrthogonalEquiv E
        (F.left x.1, perfectTotalLeftComplementEquiv E F H hR x.2) := by
  change H.left (E.left x.1 + (x.2 : Fin n → F2)) =
    E.left (F.left x.1) +
      (perfectTotalLeftComplementEquiv E F H hR x.2 : Fin n → F2)
  rw [H.left.map_add, hL x.1]
  rfl

/-- The ambient right automorphism is block diagonal in the canonical
right image-plus-annihilator decomposition. -/
theorem perfectTotal_right_orthogonal_block_diagonal
    {m n : ℕ}
    (E : BananaMatrixEmbedding (perfectBanana m) (perfectBanana n))
    (F : BananaMatrixEmbedding (perfectBanana m) (perfectBanana m))
    (H : BananaMatrixEmbedding (perfectBanana n) (perfectBanana n))
    (hL : ∀ a, H.left (E.left a) = E.left (F.left a))
    (hR : ∀ b, H.right (E.right b) = E.right (F.right b))
    (y : (Fin m → F2) ×
      (LinearMap.ker (perfectLeftPairingMap E))) :
    H.right (bananaPerfectRightOrthogonalEquiv E y) =
      bananaPerfectRightOrthogonalEquiv E
        (F.right y.1, perfectTotalRightComplementEquiv E F H hL y.2) := by
  change H.right (E.right y.1 + (y.2 : Fin n → F2)) =
    E.right (F.right y.1) +
      (perfectTotalRightComplementEquiv E F H hL y.2 : Fin n → F2)
  rw [H.right.map_add, hR y.1]
  rfl

end SuccessorTree.NonPrecompact
