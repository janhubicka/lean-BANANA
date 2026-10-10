import BANANA.NonPrecompact.BananaFinitePartialSystems

/-!
# Finite-system embeddings from partial-map squares

In the Kechris--Rosendal category of finite partial-automorphism systems,
a carrier embedding preserves the domains, ranges and partial actions.
Once the corresponding linear source maps exist and make the four
squares commute, they are automatically injective and pairing preserving.

This demonstrates that requiring genuine BANANA source embeddings
does not introduce an additional pairing-preservation hypothesis.
-/

namespace SuccessorTree.NonPrecompact

/-- Build a system embedding from a carrier embedding and compatible
linear source maps; source injectivity and pairing preservation follow
from the domain squares. -/
def BananaFinitePartialSystemEmbedding.ofLinearSourceMaps
    {n : ℕ} {S T : BananaFinitePartialSystem n}
    (f : BananaMatrixEmbedding S.carrier T.carrier)
    (u : ∀ i : Fin n,
      (Fin (S.sourceLeftDim i) → F2) →ₗ[F2]
        (Fin (T.sourceLeftDim i) → F2))
    (v : ∀ i : Fin n,
      (Fin (S.sourceRightDim i) → F2) →ₗ[F2]
        (Fin (T.sourceRightDim i) → F2))
    (hDL : ∀ i x,
      f.left ((S.domain i).left x) = (T.domain i).left (u i x))
    (hDR : ∀ i y,
      f.right ((S.domain i).right y) = (T.domain i).right (v i y))
    (hRL : ∀ i x,
      f.left ((S.range i).left x) = (T.range i).left (u i x))
    (hRR : ∀ i y,
      f.right ((S.range i).right y) = (T.range i).right (v i y)) :
    BananaFinitePartialSystemEmbedding S T := by
  let src : ∀ i : Fin n, BananaMatrixEmbedding (S.source i) (T.source i) :=
    fun i => {
      left := u i
      right := v i
      left_injective := by
        intro x y h
        apply (S.domain i).left_injective
        apply f.left_injective
        calc
          f.left ((S.domain i).left x) =
              (T.domain i).left (u i x) := hDL i x
          _ = (T.domain i).left (u i y) := by rw [h]
          _ = f.left ((S.domain i).left y) := (hDL i y).symm
      right_injective := by
        intro x y h
        apply (S.domain i).right_injective
        apply f.right_injective
        calc
          f.right ((S.domain i).right x) =
              (T.domain i).right (v i x) := hDR i x
          _ = (T.domain i).right (v i y) := by rw [h]
          _ = f.right ((S.domain i).right y) := (hDR i y).symm
      pairing_apply := by
        intro x y
        calc
          (T.source i).eval (u i x) (v i y) =
              T.carrier.eval ((T.domain i).left (u i x))
                ((T.domain i).right (v i y)) :=
              ((T.domain i).pairing_apply (u i x) (v i y)).symm
          _ = T.carrier.eval (f.left ((S.domain i).left x))
                (f.right ((S.domain i).right y)) := by
                  rw [hDL i x, hDR i y]
          _ = S.carrier.eval ((S.domain i).left x)
                ((S.domain i).right y) := f.pairing_apply _ _
          _ = (S.source i).eval x y := (S.domain i).pairing_apply x y
    }
  exact {
    carrier := f
    source := src
    domain_left := hDL
    domain_right := hDR
    range_left := hRL
    range_right := hRR
  }

end SuccessorTree.NonPrecompact
