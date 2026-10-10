import BANANA.NonPrecompact.BananaPerfectSplitSystemActions
import BANANA.NonPrecompact.BananaDirectSum

/-!
# Canonical embeddings in the split perfect-system amalgam

For B=A⊥B₀, C=A⊥C₀ and D=A⊥B₀⊥C₀, the
coordinate inclusions constructed in the previous module are linear,
injective on both sorts, preserve the perfect pairing, and agree
pointwise on the common perfect A block.

Unlike merely specifying functions, bundling these maps as genuine
BANANA embeddings discharges the embedding obligations in the
standard-coordinate perfect-total system amalgamation.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- Reconstruct a vector on a two-block coordinate space. -/
theorem bananaPerfectSplit_append_parts {a b : ℕ}
    (x : Fin (a + b) → F2) :
    Fin.append (BananaMatrixStructure.finLeftPart x)
      (BananaMatrixStructure.finRightPart x) = x := by
  funext i
  induction i using Fin.addCases <;>
    simp [BananaMatrixStructure.finLeftPart,
      BananaMatrixStructure.finRightPart]

/-- Decomposition of the perfect dot product on a finite two-block
coordinate space. -/
theorem bananaPerfectSplit_dot_parts {a b : ℕ}
    (x y : Fin (a + b) → F2) :
    x ⬝ᵥ y =
      (BananaMatrixStructure.finLeftPart x ⬝ᵥ
        BananaMatrixStructure.finLeftPart y) +
      (BananaMatrixStructure.finRightPart x ⬝ᵥ
        BananaMatrixStructure.finRightPart y) := by
  conv_lhs =>
    rw [← bananaPerfectSplit_append_parts x,
      ← bananaPerfectSplit_append_parts y,
      dotProduct_append]

/-- The inclusion B→D, as a linear map on either vector-space sort. -/
def bananaPerfectSplitLinearB (a b c : ℕ) :
    (Fin (a + b) → F2) →ₗ[F2]
      (Fin (a + (b + c)) → F2) :=
  BananaMatrixStructure.directSumLinearMap
    (LinearMap.id : (Fin a → F2) →ₗ[F2] (Fin a → F2))
    (BananaMatrixStructure.directSumLeftInl (l₁ := b) (l₂ := c))

/-- The inclusion C→D, as a linear map on either vector-space sort. -/
def bananaPerfectSplitLinearC (a b c : ℕ) :
    (Fin (a + c) → F2) →ₗ[F2]
      (Fin (a + (b + c)) → F2) :=
  BananaMatrixStructure.directSumLinearMap
    (LinearMap.id : (Fin a → F2) →ₗ[F2] (Fin a → F2))
    (BananaMatrixStructure.directSumLeftInr (l₁ := b) (l₂ := c))

@[simp] theorem bananaPerfectSplitLinearB_apply
    (a b c : ℕ) (x : Fin (a + b) → F2) :
    bananaPerfectSplitLinearB a b c x =
      bananaPerfectSplitEmbedB a b c x := rfl

@[simp] theorem bananaPerfectSplitLinearC_apply
    (a b c : ℕ) (x : Fin (a + c) → F2) :
    bananaPerfectSplitLinearC a b c x =
      bananaPerfectSplitEmbedC a b c x := rfl

theorem bananaPerfectSplitLinearB_injective (a b c : ℕ) :
    Function.Injective (bananaPerfectSplitLinearB a b c) := by
  exact BananaMatrixStructure.directSumLinearMap_injective
    (by intro x y h; exact h)
    (BananaMatrixStructure.directSumLeftInl_injective)

theorem bananaPerfectSplitLinearC_injective (a b c : ℕ) :
    Function.Injective (bananaPerfectSplitLinearC a b c) := by
  exact BananaMatrixStructure.directSumLinearMap_injective
    (by intro x y h; exact h)
    (BananaMatrixStructure.directSumLeftInr_injective)

/-- The B-inclusion preserves all cross-pairings. -/
theorem bananaPerfectSplitEmbedB_pairing (a b c : ℕ)
    (x y : Fin (a + b) → F2) :
    bananaPerfectSplitEmbedB a b c x ⬝ᵥ
      bananaPerfectSplitEmbedB a b c y = x ⬝ᵥ y := by
  calc
    bananaPerfectSplitEmbedB a b c x ⬝ᵥ
        bananaPerfectSplitEmbedB a b c y =
      (BananaMatrixStructure.finLeftPart x ⬝ᵥ
        BananaMatrixStructure.finLeftPart y) +
      (BananaMatrixStructure.finRightPart x ⬝ᵥ
        BananaMatrixStructure.finRightPart y) := by
          simp [bananaPerfectSplitEmbedB, dotProduct_append]
    _ = x ⬝ᵥ y := (bananaPerfectSplit_dot_parts x y).symm

/-- The C-inclusion preserves all cross-pairings. -/
theorem bananaPerfectSplitEmbedC_pairing (a b c : ℕ)
    (x y : Fin (a + c) → F2) :
    bananaPerfectSplitEmbedC a b c x ⬝ᵥ
      bananaPerfectSplitEmbedC a b c y = x ⬝ᵥ y := by
  calc
    bananaPerfectSplitEmbedC a b c x ⬝ᵥ
        bananaPerfectSplitEmbedC a b c y =
      (BananaMatrixStructure.finLeftPart x ⬝ᵥ
        BananaMatrixStructure.finLeftPart y) +
      (BananaMatrixStructure.finRightPart x ⬝ᵥ
        BananaMatrixStructure.finRightPart y) := by
          simp [bananaPerfectSplitEmbedC, dotProduct_append]
    _ = x ⬝ᵥ y := (bananaPerfectSplit_dot_parts x y).symm

/-- The embedding of the first perfect total subsystem. -/
def bananaPerfectSplitEmbeddingB (a b c : ℕ) :
    BananaMatrixEmbedding
      (perfectBanana (a + b))
      (perfectBanana (a + (b + c))) where
  left := bananaPerfectSplitLinearB a b c
  right := bananaPerfectSplitLinearB a b c
  left_injective := bananaPerfectSplitLinearB_injective a b c
  right_injective := bananaPerfectSplitLinearB_injective a b c
  pairing_apply := by
    intro x y
    simpa only [perfectBanana_eval, bananaPerfectSplitLinearB_apply] using
      bananaPerfectSplitEmbedB_pairing a b c x y

/-- The embedding of the second perfect total subsystem. -/
def bananaPerfectSplitEmbeddingC (a b c : ℕ) :
    BananaMatrixEmbedding
      (perfectBanana (a + c))
      (perfectBanana (a + (b + c))) where
  left := bananaPerfectSplitLinearC a b c
  right := bananaPerfectSplitLinearC a b c
  left_injective := bananaPerfectSplitLinearC_injective a b c
  right_injective := bananaPerfectSplitLinearC_injective a b c
  pairing_apply := by
    intro x y
    simpa only [perfectBanana_eval, bananaPerfectSplitLinearC_apply] using
      bananaPerfectSplitEmbedC_pairing a b c x y

/-- The two embeddings agree on the first common perfect block, on
both sorts simultaneously. -/
theorem bananaPerfectSplitEmbeddings_agree_common
    (a b c : ℕ) (x : Fin a → F2) :
    (bananaPerfectSplitEmbeddingB a b c).left
      (Fin.append x (0 : Fin b → F2)) =
    (bananaPerfectSplitEmbeddingC a b c).left
      (Fin.append x (0 : Fin c → F2)) ∧
    (bananaPerfectSplitEmbeddingB a b c).right
      (Fin.append x (0 : Fin b → F2)) =
    (bananaPerfectSplitEmbeddingC a b c).right
      (Fin.append x (0 : Fin c → F2)) := by
  constructor <;>
    simp [bananaPerfectSplitEmbeddingB, bananaPerfectSplitEmbeddingC,
      bananaPerfectSplitEmbedB, bananaPerfectSplitEmbedC]

end SuccessorTree.NonPrecompact
