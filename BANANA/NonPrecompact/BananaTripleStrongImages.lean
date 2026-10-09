import BANANA.NonPrecompact.BananaTripleCoordinates

/-!
# Exact intersection of the redundant triple-coordinate inclusions

The embeddings of B and C into A ⊕ B ⊕ C are assembled from linear
retractions of the given common-source embeddings. This file proves
that the B- and C-only coordinates are exactly the respective
remainders after subtracting the common-source contribution.

Consequently the inclusions are injective, agree on the common
source, and meet nowhere else. All assertions are purely linear;
preservation of the bilinear pairing is proved separately.
-/

namespace SuccessorTree.NonPrecompact

open BananaMatrixStructure

/-- The B-only coordinate of the inclusion from B. -/
theorem tripleProjB_inl
    {a b c : ℕ}
    (f : (Fin a → F2) →ₗ[F2] (Fin b → F2))
    (p : (Fin b → F2) →ₗ[F2] (Fin a → F2))
    (x : Fin b → F2) :
    (tripleProjB (a := a) (b := b) (c := c))
        (tripleInl (c := c) f p x) = x - f (p x) := by
  funext i
  simp [tripleProjB, tripleInl, finRightPartLinear,
    finLeftPartLinear, finAppendLinear, finLeftPart, finRightPart,
    LinearMap.sub_apply, LinearMap.comp_apply]

/-- The C-only coordinate of the inclusion from B is zero. -/
theorem tripleProjC_inl
    {a b c : ℕ}
    (f : (Fin a → F2) →ₗ[F2] (Fin b → F2))
    (p : (Fin b → F2) →ₗ[F2] (Fin a → F2))
    (x : Fin b → F2) :
    (tripleProjC (a := a) (b := b) (c := c))
        (tripleInl (c := c) f p x) = 0 := by
  funext i
  simp [tripleProjC, tripleInl, finRightPartLinear,
    finAppendLinear, finRightPart]

/-- The B-only coordinate of the inclusion from C is zero. -/
theorem tripleProjB_inr
    {a b c : ℕ}
    (g : (Fin a → F2) →ₗ[F2] (Fin c → F2))
    (p : (Fin c → F2) →ₗ[F2] (Fin a → F2))
    (x : Fin c → F2) :
    (tripleProjB (a := a) (b := b) (c := c))
        (tripleInr (b := b) g p x) = 0 := by
  funext i
  simp [tripleProjB, tripleInr, finRightPartLinear,
    finLeftPartLinear, finAppendLinear, finLeftPart, finRightPart]

/-- The C-only coordinate of the inclusion from C. -/
theorem tripleProjC_inr
    {a b c : ℕ}
    (g : (Fin a → F2) →ₗ[F2] (Fin c → F2))
    (p : (Fin c → F2) →ₗ[F2] (Fin a → F2))
    (x : Fin c → F2) :
    (tripleProjC (a := a) (b := b) (c := c))
        (tripleInr (b := b) g p x) = x - g (p x) := by
  funext i
  simp [tripleProjC, tripleInr, finRightPartLinear,
    finAppendLinear, finRightPart,
    LinearMap.sub_apply, LinearMap.comp_apply]

/-- Inclusion of B is injective, without any assumption on the maps
f and p: both the projection p(x) and the remainder x-f(p(x))
are recorded. -/
theorem tripleInl_injective
    {a b c : ℕ}
    (f : (Fin a → F2) →ₗ[F2] (Fin b → F2))
    (p : (Fin b → F2) →ₗ[F2] (Fin a → F2)) :
    Function.Injective (tripleInl (c := c) f p) := by
  intro x y h
  have hA : p x = p y := by
    have hp := congrArg (tripleProjA (a := a) (b := b) (c := c)) h
    simpa only [tripleProjA_inl] using hp
  have hB : x - f (p x) = y - f (p y) := by
    have hp := congrArg (tripleProjB (a := a) (b := b) (c := c)) h
    simpa only [tripleProjB_inl] using hp
  calc
    x = x - f (p x) + f (p x) := by abel
    _ = y - f (p y) + f (p y) := by rw [hB, hA]
    _ = y := by abel

/-- Symmetric injectivity of the inclusion from C. -/
theorem tripleInr_injective
    {a b c : ℕ}
    (g : (Fin a → F2) →ₗ[F2] (Fin c → F2))
    (p : (Fin c → F2) →ₗ[F2] (Fin a → F2)) :
    Function.Injective (tripleInr (b := b) g p) := by
  intro x y h
  have hA : p x = p y := by
    have hp := congrArg (tripleProjA (a := a) (b := b) (c := c)) h
    simpa only [tripleProjA_inr] using hp
  have hC : x - g (p x) = y - g (p y) := by
    have hp := congrArg (tripleProjC (a := a) (b := b) (c := c)) h
    simpa only [tripleProjC_inr] using hp
  calc
    x = x - g (p x) + g (p x) := by abel
    _ = y - g (p y) + g (p y) := by rw [hC, hA]
    _ = y := by abel

end SuccessorTree.NonPrecompact
