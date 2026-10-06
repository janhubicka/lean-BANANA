import BANANA.NonPrecompact.Completion
import BANANA.NonPrecompact.PerfectLeftRange

/-!
# Binary subspace Ramsey interface for one-sided BANANA copies

This module isolates the only external combinatorial input in the degree-one
half of the BANANA copy-Ramsey classification.

A fixed-dimensional copy in a one-sided BANANA structure is exactly a
fixed-dimensional vector subspace.  We therefore state the binary
Graham--Leeb--Rothschild property directly for finite coordinate spaces and
prove that this property implies the Ramsey-degree-one assertion needed by
the manuscript.

No form of GLR is assumed as an axiom here: the main theorems below are
conditional on the explicit proposition `BinarySubspaceRamsey`.
-/

namespace SuccessorTree.NonPrecompact

open LinearMap Module

/-- A d-dimensional subspace of the standard binary coordinate space F₂^n. -/
abbrev FixedSubspace (d n : ℕ) :=
  {W : Submodule F2 (Fin n → F2) // finrank F2 W = d}

namespace FixedSubspace

/-- Push a fixed-dimensional subspace through an injective linear map. -/
noncomputable def map
    {d n m : ℕ}
    (P : FixedSubspace d n)
    (f : (Fin n → F2) →ₗ[F2] (Fin m → F2))
    (hf : Function.Injective f) :
    FixedSubspace d m := by
  refine ⟨LinearMap.range (f.comp P.1.subtype), ?_⟩
  have hinj : Function.Injective (f.comp P.1.subtype) :=
    hf.comp P.1.injective_subtype
  exact (LinearMap.finrank_range_of_inj hinj).trans P.2

/-- The image of a subspace is contained in the range of the ambient map. -/
theorem map_le_range
    {d n m : ℕ}
    (P : FixedSubspace d n)
    (f : (Fin n → F2) →ₗ[F2] (Fin m → F2))
    (hf : Function.Injective f) :
    (P.map f hf).1 ≤ LinearMap.range f := by
  rintro z ⟨x, rfl⟩
  exact ⟨x.1, rfl⟩

end FixedSubspace

/-- The finite binary subspace Ramsey theorem, stated only in the form used
by the BANANA manuscript.

For every a ≤ D and finite colour set there is an ambient dimension D+k
such that every colouring of the a-dimensional subspaces has a D-dimensional
subspace all of whose a-dimensional subspaces have one colour. -/
def BinarySubspaceRamsey : Prop :=
  ∀ (a D colours : ℕ), a ≤ D → 0 < colours →
    ∃ k : ℕ,
      ∀ colouring : FixedSubspace a (D + k) → Fin colours,
        ∃ W : FixedSubspace D (D + k), ∃ c : Fin colours,
          ∀ P : FixedSubspace a (D + k),
            P.1 ≤ W.1 → colouring P = c

/-- Copy-Ramsey-degree one for an a-dimensional source supported only on the
left sort, expressed in terms of copy ranges.

The target is an arbitrary finite BANANA structure.  The witness may be
taken to be a standard perfect pairing. -/
def LeftOneSidedCopyRamseyOne (a : ℕ) : Prop :=
  ∀ (l r : ℕ) (B : BananaMatrixStructure l r)
      (colours : ℕ), 0 < colours →
    ∃ n : ℕ,
      ∀ colouring : FixedSubspace a n → Fin colours,
        ∃ F : BananaMatrixEmbedding B (perfectBanana n),
          ∃ c : Fin colours,
            ∀ P : FixedSubspace a l,
              colouring (P.map F.left F.left_injective) = c

/-- The symmetric right-sort version of one-sided copy Ramsey degree one. -/
def RightOneSidedCopyRamseyOne (a : ℕ) : Prop :=
  ∀ (l r : ℕ) (B : BananaMatrixStructure l r)
      (colours : ℕ), 0 < colours →
    ∃ n : ℕ,
      ∀ colouring : FixedSubspace a n → Fin colours,
        ∃ F : BananaMatrixEmbedding B (perfectBanana n),
          ∃ c : Fin colours,
            ∀ P : FixedSubspace a r,
              colouring (P.map F.right F.right_injective) = c

/-- The binary subspace Ramsey theorem implies the left one-sided
degree-one assertion used in `thm:banana-degree-classification`. -/
theorem leftOneSidedCopyRamseyOne_of_binarySubspaceRamsey
    (hGLR : BinarySubspaceRamsey)
    (a : ℕ) :
    LeftOneSidedCopyRamseyOne a := by
  intro l r B colours hcolours
  let D : ℕ := (l + r) + a
  have haD : a ≤ D := by
    dsimp [D]
    omega
  obtain ⟨k, hk⟩ := hGLR a D colours haD hcolours
  refine ⟨D + k, ?_⟩
  intro colouring
  obtain ⟨W, c, hmono⟩ := hk colouring
  obtain ⟨E, hE⟩ :=
    BananaMatrixStructure.exists_perfectBlockEmbedding_leftRange_eq
      W.1 W.2
  let j₀ : BananaMatrixEmbedding B (perfectBanana (l + r)) :=
    B.completionEmbedding
  let j₁ :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana D) := by
    simpa [D, Nat.add_assoc] using
      BananaMatrixStructure.standardPerfectBlockEmbedding (l + r) a
  let j : BananaMatrixEmbedding B (perfectBanana D) :=
    BananaMatrixEmbedding.comp j₁ j₀
  let F : BananaMatrixEmbedding B (perfectBanana (D + k)) :=
    BananaMatrixEmbedding.comp E j
  refine ⟨F, c, ?_⟩
  intro P
  apply hmono
  have hmap :
      (P.map F.left F.left_injective).1 ≤
        LinearMap.range F.left :=
    P.map_le_range F.left F.left_injective
  apply hmap.trans
  rw [← hE]
  change LinearMap.range F.left ≤ LinearMap.range E.left
  simpa [F, BananaMatrixEmbedding.comp] using
    LinearMap.range_comp_le_range j.left E.left

/-- The binary subspace Ramsey theorem also implies the right one-sided
degree-one assertion. -/
theorem rightOneSidedCopyRamseyOne_of_binarySubspaceRamsey
    (hGLR : BinarySubspaceRamsey)
    (a : ℕ) :
    RightOneSidedCopyRamseyOne a := by
  intro l r B colours hcolours
  let D : ℕ := (l + r) + a
  have haD : a ≤ D := by
    dsimp [D]
    omega
  obtain ⟨k, hk⟩ := hGLR a D colours haD hcolours
  refine ⟨D + k, ?_⟩
  intro colouring
  obtain ⟨W, c, hmono⟩ := hk colouring
  obtain ⟨E, hE⟩ :=
    BananaMatrixStructure.exists_perfectBlockEmbedding_rightRange_eq
      W.1 W.2
  let j₀ : BananaMatrixEmbedding B (perfectBanana (l + r)) :=
    B.completionEmbedding
  let j₁ :
      BananaMatrixEmbedding
        (perfectBanana (l + r))
        (perfectBanana D) := by
    simpa [D, Nat.add_assoc] using
      BananaMatrixStructure.standardPerfectBlockEmbedding (l + r) a
  let j : BananaMatrixEmbedding B (perfectBanana D) :=
    BananaMatrixEmbedding.comp j₁ j₀
  let F : BananaMatrixEmbedding B (perfectBanana (D + k)) :=
    BananaMatrixEmbedding.comp E j
  refine ⟨F, c, ?_⟩
  intro P
  apply hmono
  have hmap :
      (P.map F.right F.right_injective).1 ≤
        LinearMap.range F.right :=
    P.map_le_range F.right F.right_injective
  apply hmap.trans
  rw [← hE]
  change LinearMap.range F.right ≤ LinearMap.range E.right
  simpa [F, BananaMatrixEmbedding.comp] using
    LinearMap.range_comp_le_range j.right E.right

end SuccessorTree.NonPrecompact
