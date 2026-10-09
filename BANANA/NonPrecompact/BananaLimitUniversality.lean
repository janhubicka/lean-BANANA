import BANANA.NonPrecompact.BananaLimitPerfectEmbedding
import BANANA.NonPrecompact.Completion

/-!
# Universality of the explicit countable BANANA pairing

Every finite BANANA matrix pairing embeds into a standard perfect
pairing of dimension l+r by the previously verified completion
construction. Every such perfect pairing is realised on a finite
rational-coordinate block of the explicit countable pairing. Their
composition is therefore a genuine embedding of two-sorted bilinear
systems into the explicit countable BANANA model.

This formalises the universality direction of age equality.
The converse (every finite generated substructure is of finite
matrix type) and global homogeneity remain separate obligations.
-/

namespace SuccessorTree.NonPrecompact

/-- A pairing-preserving embedding of a finite standard-coordinate
BANANA structure into the two-sorted finite-support limit. -/
structure BananaMatrixEmbeddingToLimit
    {l r : ℕ} (A : BananaMatrixStructure l r) where
  left : (Fin l → F2) →ₗ[F2] BananaLimitVector
  right : (Fin r → F2) →ₗ[F2] BananaLimitVector
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  pairing_apply :
    ∀ x y, bananaLimitPairing (left x) (right y) = A.eval x y

/-- Every standard perfect finite pairing embeds in the concrete
rational-coordinate BANANA limit. -/
theorem perfectBanana_embeds_in_limit (n : ℕ) :
    Nonempty (BananaMatrixEmbeddingToLimit (perfectBanana n)) := by
  classical
  obtain ⟨S, E, hE⟩ := exists_perfect_block_in_banana_limit n
  let f : (Fin n → F2) →ₗ[F2] BananaLimitVector :=
    (bananaLimitBlock S).subtype.comp E.toLinearMap
  refine ⟨{
    left := f
    right := f
    left_injective := (bananaLimitBlock S).injective_subtype.comp E.injective
    right_injective := (bananaLimitBlock S).injective_subtype.comp E.injective
    pairing_apply := ?_
  }⟩
  intro x y
  change bananaLimitPairing (E x : BananaLimitVector)
    (E y : BananaLimitVector) = (perfectBanana n).eval x y
  simpa only [perfectBanana_eval] using hE x y

/-- Universality: every finite BANANA pairing embeds into the
explicit countable pairing on finitely supported rational coordinates. -/
theorem BananaMatrixStructure.embeds_in_explicit_limit
    {l r : ℕ} (A : BananaMatrixStructure l r) :
    Nonempty (BananaMatrixEmbeddingToLimit A) := by
  classical
  obtain ⟨P⟩ := perfectBanana_embeds_in_limit (l + r)
  let f : BananaMatrixEmbedding A (perfectBanana (l + r)) :=
    A.completionEmbedding
  refine ⟨{
    left := P.left.comp f.left
    right := P.right.comp f.right
    left_injective := P.left_injective.comp f.left_injective
    right_injective := P.right_injective.comp f.right_injective
    pairing_apply := ?_
  }⟩
  intro x y
  exact (P.pairing_apply (f.left x) (f.right y)).trans
    (f.pairing_apply x y)

end SuccessorTree.NonPrecompact
