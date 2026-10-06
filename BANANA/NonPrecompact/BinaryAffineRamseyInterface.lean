import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import BANANA.NonPrecompact.BinarySubspaceRamseyInterface

/-!
# Affine-to-linear reduction for binary subspace Ramsey

Spencer's proof of the Graham--Leeb--Rothschild theorem first establishes an
affine Ramsey theorem and then passes to linear subspaces by colouring an
affine space according to the colour of its direction.

This file formalises that final reduction.  It leaves the affine theorem as
an explicit proposition, so the remaining combinatorial work is isolated
from the BANANA-specific linear algebra.
-/

namespace SuccessorTree.NonPrecompact

open Module

/-- A nonempty d-dimensional affine subspace of the standard binary
coordinate space F₂^n. -/
structure FixedAffineSubspace (d n : ℕ) where
  space : AffineSubspace F2 (Fin n → F2)
  nonempty : (space : Set (Fin n → F2)).Nonempty
  finrank_direction : finrank F2 space.direction = d

/-- The affine finite-vector-space Ramsey theorem in the form used by
Spencer's reduction. -/
def BinaryAffineSubspaceRamsey : Prop :=
  ∀ (a D colours : ℕ), a ≤ D → 0 < colours →
    ∃ k : ℕ,
      ∀ colouring : FixedAffineSubspace a (D + k) → Fin colours,
        ∃ W : FixedAffineSubspace D (D + k), ∃ c : Fin colours,
          ∀ P : FixedAffineSubspace a (D + k),
            P.space ≤ W.space → colouring P = c

/-- The affine binary Ramsey theorem implies the linear binary subspace
Ramsey theorem by colouring an affine space with the colour of its
direction. -/
theorem binarySubspaceRamsey_of_binaryAffineSubspaceRamsey
    (hAff : BinaryAffineSubspaceRamsey) :
    BinarySubspaceRamsey := by
  intro a D colours haD hcolours
  obtain ⟨k, hk⟩ := hAff a D colours haD hcolours
  refine ⟨k, ?_⟩
  intro colouring
  let affineColour :
      FixedAffineSubspace a (D + k) → Fin colours :=
    fun P => colouring ⟨P.space.direction, P.finrank_direction⟩
  obtain ⟨W, c, hmono⟩ := hk affineColour
  let Wdir : FixedSubspace D (D + k) :=
    ⟨W.space.direction, W.finrank_direction⟩
  refine ⟨Wdir, c, ?_⟩
  intro P hPW
  let p : Fin (D + k) → F2 := Classical.choose W.nonempty
  have hp : p ∈ W.space := Classical.choose_spec W.nonempty
  let Tspace : AffineSubspace F2 (Fin (D + k) → F2) :=
    AffineSubspace.mk' p P.1
  let T : FixedAffineSubspace a (D + k) :=
    { space := Tspace
      nonempty := AffineSubspace.mk'_nonempty p P.1
      finrank_direction := by
        change finrank F2 (AffineSubspace.mk' p P.1).direction = a
        rw [AffineSubspace.direction_mk']
        exact P.2 }
  have hTle : T.space ≤ W.space := by
    intro q hq
    have hqdir : q -ᵥ p ∈ P.1 := by
      exact AffineSubspace.mem_mk'.mp hq
    have hqW : q -ᵥ p ∈ W.space.direction :=
      hPW hqdir
    rw [← vsub_vadd q p]
    exact (W.space.vadd_mem_iff_mem_direction _ hp).2 hqW
  have hTc := hmono T hTle
  simpa [affineColour, T, Tspace, AffineSubspace.direction_mk'] using hTc

end SuccessorTree.NonPrecompact
