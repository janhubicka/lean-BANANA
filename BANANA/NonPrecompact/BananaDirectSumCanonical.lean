import BANANA.NonPrecompact.BananaDirectSum

/-!
# Canonical empty-base amalgamation for finite BANANA pairings

The empty-generated BANANA structure has precisely the two named zero
vectors. The block-diagonal direct sum is its canonical amalgam.

This module completes the finite-category verification used in the
circulation corollary contrasting definable Ramsey colourings with
unrestricted copy colourings: the canonical inclusions meet exactly
in the two zero elements, and are natural in both source structures.

The model-theoretic implication to DEERP remains a cited standard
result and is not reproved here.
-/

namespace SuccessorTree.NonPrecompact

namespace BananaMatrixStructure

variable {l₁ r₁ l₂ r₂ : ℕ}
variable (A : BananaMatrixStructure l₁ r₁)
variable (B : BananaMatrixStructure l₂ r₂)

/-- The canonical first-block inclusion has the original first component. -/
@[simp] private theorem prebanana_finLeftPart_append_left
    {m n : ℕ} (x : Fin m → F2) :
    finLeftPart (Fin.append x (0 : Fin n → F2)) = x := by
  funext i
  simp [finLeftPart]

/-- The second component of the first-block inclusion is zero. -/
@[simp] private theorem prebanana_finRightPart_append_left
    {m n : ℕ} (x : Fin m → F2) :
    finRightPart (Fin.append x (0 : Fin n → F2)) = 0 := by
  funext i
  simp [finRightPart]

/-- The first component of the second-block inclusion is zero. -/
@[simp] private theorem prebanana_finLeftPart_append_right
    {m n : ℕ} (x : Fin n → F2) :
    finLeftPart (Fin.append (0 : Fin m → F2) x) = 0 := by
  funext i
  simp [finLeftPart]

/-- The second-block inclusion has the original second component. -/
@[simp] private theorem prebanana_finRightPart_append_right
    {m n : ℕ} (x : Fin n → F2) :
    finRightPart (Fin.append (0 : Fin m → F2) x) = x := by
  funext i
  simp [finRightPart]


/-- Images of the two canonical left-sort inclusions intersect
exactly in the named zero vector. -/
theorem directSum_inl_inr_eq_iff_zero_left
    (x : Fin l₁ → F2) (y : Fin l₂ → F2) :
    directSumLeftInl x = (directSumLeftInr y :
      Fin (l₁ + l₂) → F2) ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · funext i
      have hi := congrFun h (Fin.castAdd l₂ i)
      simpa [directSumLeftInl, directSumLeftInr] using hi
    · funext i
      have hi := congrFun h (Fin.natAdd l₁ i)
      simpa [directSumLeftInl, directSumLeftInr] using hi.symm
  · rintro ⟨rfl, rfl⟩
    simp

/-- Images of the canonical right-sort inclusions meet exactly
in the named zero vector as well. -/
theorem directSum_inl_inr_eq_iff_zero_right
    (x : Fin r₁ → F2) (y : Fin r₂ → F2) :
    directSumRightInl x = (directSumRightInr y :
      Fin (r₁ + r₂) → F2) ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · funext i
      have hi := congrFun h (Fin.castAdd r₂ i)
      simpa [directSumRightInl, directSumRightInr] using hi
    · funext i
      have hi := congrFun h (Fin.natAdd r₁ i)
      simpa [directSumRightInl, directSumRightInr] using hi.symm
  · rintro ⟨rfl, rfl⟩
    simp

/-- Functoriality of the first canonical inclusion on the left sort. -/
theorem directSum_natural_inl_left
    {l₁' r₁' l₂' r₂' : ℕ}
    {A' : BananaMatrixStructure l₁' r₁'}
    {B' : BananaMatrixStructure l₂' r₂'}
    (f : BananaMatrixEmbedding A A')
    (g : BananaMatrixEmbedding B B') :
    (BananaMatrixEmbedding.comp (directSumEmbedding A B f g)
        (A.directSumInlEmbedding B)).left =
      (BananaMatrixEmbedding.comp (A'.directSumInlEmbedding B') f).left := by
  apply LinearMap.ext
  intro x
  change
    Fin.append (f.left (finLeftPart (Fin.append x 0)))
      (g.left (finRightPart (Fin.append x 0))) =
    Fin.append (f.left x) 0
  simp [prebanana_finLeftPart_append_left,
    prebanana_finRightPart_append_left,
    prebanana_finLeftPart_append_right,
    prebanana_finRightPart_append_right]

/-- Functoriality of the first inclusion on the right sort. -/
theorem directSum_natural_inl_right
    {l₁' r₁' l₂' r₂' : ℕ}
    {A' : BananaMatrixStructure l₁' r₁'}
    {B' : BananaMatrixStructure l₂' r₂'}
    (f : BananaMatrixEmbedding A A')
    (g : BananaMatrixEmbedding B B') :
    (BananaMatrixEmbedding.comp (directSumEmbedding A B f g)
        (A.directSumInlEmbedding B)).right =
      (BananaMatrixEmbedding.comp (A'.directSumInlEmbedding B') f).right := by
  apply LinearMap.ext
  intro x
  change
    Fin.append (f.right (finLeftPart (Fin.append x 0)))
      (g.right (finRightPart (Fin.append x 0))) =
    Fin.append (f.right x) 0
  simp [prebanana_finLeftPart_append_left,
    prebanana_finRightPart_append_left,
    prebanana_finLeftPart_append_right,
    prebanana_finRightPart_append_right]

/-- Functoriality of the second canonical inclusion on the left sort. -/
theorem directSum_natural_inr_left
    {l₁' r₁' l₂' r₂' : ℕ}
    {A' : BananaMatrixStructure l₁' r₁'}
    {B' : BananaMatrixStructure l₂' r₂'}
    (f : BananaMatrixEmbedding A A')
    (g : BananaMatrixEmbedding B B') :
    (BananaMatrixEmbedding.comp (directSumEmbedding A B f g)
        (A.directSumInrEmbedding B)).left =
      (BananaMatrixEmbedding.comp (A'.directSumInrEmbedding B') g).left := by
  apply LinearMap.ext
  intro x
  change
    Fin.append (f.left (finLeftPart (Fin.append 0 x)))
      (g.left (finRightPart (Fin.append 0 x))) =
    Fin.append 0 (g.left x)
  simp [prebanana_finLeftPart_append_left,
    prebanana_finRightPart_append_left,
    prebanana_finLeftPart_append_right,
    prebanana_finRightPart_append_right]

/-- Functoriality of the second canonical inclusion on the right sort. -/
theorem directSum_natural_inr_right
    {l₁' r₁' l₂' r₂' : ℕ}
    {A' : BananaMatrixStructure l₁' r₁'}
    {B' : BananaMatrixStructure l₂' r₂'}
    (f : BananaMatrixEmbedding A A')
    (g : BananaMatrixEmbedding B B') :
    (BananaMatrixEmbedding.comp (directSumEmbedding A B f g)
        (A.directSumInrEmbedding B)).right =
      (BananaMatrixEmbedding.comp (A'.directSumInrEmbedding B') g).right := by
  apply LinearMap.ext
  intro x
  change
    Fin.append (f.right (finLeftPart (Fin.append 0 x)))
      (g.right (finRightPart (Fin.append 0 x))) =
    Fin.append 0 (g.right x)
  simp [prebanana_finLeftPart_append_left,
    prebanana_finRightPart_append_left,
    prebanana_finLeftPart_append_right,
    prebanana_finRightPart_append_right]

/-- The direct sum witnesses strong amalgamation over the two named
zero elements, with vanishing cross-pairings on both sorts. -/
theorem exists_canonical_zero_amalgam :
    ∃ D : BananaMatrixStructure (l₁ + l₂) (r₁ + r₂),
    ∃ eA : BananaMatrixEmbedding A D,
    ∃ eB : BananaMatrixEmbedding B D,
      (∀ x y, eA.left x = eB.left y ↔ x = 0 ∧ y = 0) ∧
      (∀ x y, eA.right x = eB.right y ↔ x = 0 ∧ y = 0) ∧
      (∀ x y, D.eval (eA.left x) (eB.right y) = 0) ∧
      (∀ x y, D.eval (eB.left x) (eA.right y) = 0) := by
  refine ⟨bananaDirectSum A B, A.directSumInlEmbedding B,
    A.directSumInrEmbedding B, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact directSum_inl_inr_eq_iff_zero_left x y
  · intro x y
    exact directSum_inl_inr_eq_iff_zero_right x y
  · intro x y
    exact A.directSum_cross_pairing_left_right B x y
  · intro x y
    exact A.directSum_cross_pairing_right_left B x y

end BananaMatrixStructure

end SuccessorTree.NonPrecompact
