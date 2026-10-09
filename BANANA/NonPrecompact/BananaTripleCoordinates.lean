import BANANA.NonPrecompact.BananaArbitraryAmalgamTools
import BANANA.NonPrecompact.BananaDirectSum

/-!
# Redundant triple coordinates for arbitrary BANANA amalgamation

For arbitrary embeddings A → B and A → C, choose linear retractions
on each sort. Instead of quotienting a direct sum, use the redundant
coordinate space A ⊕ B ⊕ C. The two embeddings into this space have
the following forms:

  b ↦ (p_B(b), b - f(p_B(b)), 0)
  c ↦ (p_C(c), 0, c - g(p_C(c))).

This file provides reusable linear maps for the three coordinate
projections and the two inclusions. The pairing itself is constructed
later by adding the pullbacks of B, C and A, with the A-term
subtracted to correct the double counting.

No complete strong-amalgamation theorem is asserted here.
-/

namespace SuccessorTree.NonPrecompact

open BananaMatrixStructure

/-- Linear projection to the first part of a finite binary direct sum. -/
def finLeftPartLinear {a b : ℕ} :
    (Fin (a + b) → F2) →ₗ[F2] (Fin a → F2) where
  toFun := finLeftPart
  map_add' x y := finLeftPart_add x y
  map_smul' c x := finLeftPart_smul c x

/-- Linear projection to the second part of a finite binary direct sum. -/
def finRightPartLinear {a b : ℕ} :
    (Fin (a + b) → F2) →ₗ[F2] (Fin b → F2) where
  toFun := finRightPart
  map_add' x y := finRightPart_add x y
  map_smul' c x := finRightPart_smul c x

/-- Pair two linear maps with a common source by appending their
coordinate vectors, retaining linearity. -/
def finAppendLinear
    {M : Type*} [AddCommMonoid M] [Module F2 M]
    {a b : ℕ}
    (f : M →ₗ[F2] (Fin a → F2))
    (g : M →ₗ[F2] (Fin b → F2)) :
    M →ₗ[F2] (Fin (a + b) → F2) where
  toFun x := Fin.append (f x) (g x)
  map_add' x y := by
    funext i
    induction i using Fin.addCases <;> simp
  map_smul' c x := by
    funext i
    induction i using Fin.addCases <;> simp

/-- Projection to the shared A-block of a triple coordinate space. -/
def tripleProjA {a b c : ℕ} :
    (Fin ((a + b) + c) → F2) →ₗ[F2] (Fin a → F2) :=
  (finLeftPartLinear (a := a) (b := b)).comp
    (finLeftPartLinear (a := a + b) (b := c))

/-- Projection to the B-only block of a triple coordinate space. -/
def tripleProjB {a b c : ℕ} :
    (Fin ((a + b) + c) → F2) →ₗ[F2] (Fin b → F2) :=
  (finRightPartLinear (a := a) (b := b)).comp
    (finLeftPartLinear (a := a + b) (b := c))

/-- Projection to the C-only block of a triple coordinate space. -/
def tripleProjC {a b c : ℕ} :
    (Fin ((a + b) + c) → F2) →ₗ[F2] (Fin c → F2) :=
  finRightPartLinear (a := a + b) (b := c)

/-- The inclusion of B into A ⊕ B ⊕ C, using any linear retraction
p of f. This definition is meaningful even before p ∘ f = id is
assumed; the retraction identity is needed for the common embedding. -/
def tripleInl
    {a b c : ℕ}
    (f : (Fin a → F2) →ₗ[F2] (Fin b → F2))
    (p : (Fin b → F2) →ₗ[F2] (Fin a → F2)) :
    (Fin b → F2) →ₗ[F2] (Fin ((a + b) + c) → F2) :=
  finAppendLinear
    (finAppendLinear p (LinearMap.id - f.comp p))
    (0 : (Fin b → F2) →ₗ[F2] (Fin c → F2))

/-- Symmetric inclusion of C, with the B-only coordinate block zero. -/
def tripleInr
    {a b c : ℕ}
    (g : (Fin a → F2) →ₗ[F2] (Fin c → F2))
    (p : (Fin c → F2) →ₗ[F2] (Fin a → F2)) :
    (Fin c → F2) →ₗ[F2] (Fin ((a + b) + c) → F2) :=
  finAppendLinear
    (finAppendLinear p
      (0 : (Fin c → F2) →ₗ[F2] (Fin b → F2)))
    (LinearMap.id - g.comp p)

/-- Projecting to the common coordinates after including a B vector
recovers the chosen retraction of that vector. -/
theorem tripleProjA_inl
    {a b c : ℕ}
    (f : (Fin a → F2) →ₗ[F2] (Fin b → F2))
    (p : (Fin b → F2) →ₗ[F2] (Fin a → F2))
    (x : Fin b → F2) :
    (tripleProjA (a := a) (b := b) (c := c)) (tripleInl f p x) = p x := by
  funext i
  simp [tripleProjA, finLeftPartLinear, tripleInl,
    finAppendLinear, finLeftPart]

/-- The analogous common-coordinate projection for a C vector. -/
theorem tripleProjA_inr
    {a b c : ℕ}
    (g : (Fin a → F2) →ₗ[F2] (Fin c → F2))
    (p : (Fin c → F2) →ₗ[F2] (Fin a → F2))
    (x : Fin c → F2) :
    (tripleProjA (a := a) (b := b) (c := c)) (tripleInr g p x) = p x := by
  funext i
  simp [tripleProjA, finLeftPartLinear, tripleInr,
    finAppendLinear, finLeftPart]

end SuccessorTree.NonPrecompact
