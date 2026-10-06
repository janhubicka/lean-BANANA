import BANANA.NonPrecompact.BinarySubspaceRamseyInterface
import SuccessorTree.ShapeFiniteCorollaries

/-!
# Transfer from finite successor Ramsey to binary subspace Ramsey

This file isolates the representation boundary in the reduction of binary GLR
to the finite exact-terminal successor-tree theorem.

A concrete successor-tree encoding supplies a range map from exact finite
approximations to fixed-dimensional binary subspaces and a factorisation
property saying that every smaller subspace of a represented range is obtained
by right composition with a smaller exact approximation.  Under precisely
those hypotheses, the finite exact successor Ramsey theorem gives the binary
subspace Ramsey theorem directly.
-/

namespace SuccessorTree.NonPrecompact

open Module

universe u v

variable {T : Type u} {Label : Type v}
variable [PartialOrder T] [LevelTree T]
variable {S : STree T Label}

/-- Representation interface needed to read exact finite successor-tree
approximations as binary vector-space copies.

Width is `d+1`: an exact approximation through source level `d` encodes
the action on the whole coordinate space `F₂^d`. -/
structure BinarySubspaceSuccessorEncoding (H : SMTree S) where
  toSubspace :
    ∀ {d N : ℕ},
      SMTree.AM.At H 0 (d + 1) N →
        FixedSubspace d N
  coordinate_nonempty :
    ∀ {a D : ℕ}, a ≤ D →
      Nonempty
        (SMTree.AM.At H 0 (a + 1) (D + 1 - 1))
  factor :
    ∀ {a D N : ℕ} (haD : a ≤ D)
      (f : SMTree.AM.At H 0 (D + 1) N)
      (P : FixedSubspace a N),
      P.1 ≤ (toSubspace f).1 →
        ∃ g : SMTree.AM.At H 0 (a + 1) (D + 1 - 1),
          toSubspace
              (SMTree.exactComp H
                (by omega : 0 < D + 1)
                (by omega : 0 < a + 1)
                f g) =
            P

/-- The finite exact-terminal successor theorem implies binary GLR once the
copy-range encoding and its composition/factorisation law are supplied. -/
theorem binarySubspaceRamsey_of_successorEncoding
    (H : SMTree S)
    (E : BinarySubspaceSuccessorEncoding H) :
    BinarySubspaceRamsey := by
  intro a D colours haD hcolours
  letI : Nonempty (Fin colours) := ⟨⟨0, hcolours⟩⟩
  obtain ⟨N, hN⟩ :=
    SMTree.shapeRamsey_exact
      (κ := Fin colours) H 0 (a + 1) (D + 1)
      (by omega) (by omega)

  have hDN : D ≤ N := by
    let dummy :
        SMTree.AM.At H 0 (a + 1) N → Fin colours :=
      fun _ => ⟨0, hcolours⟩
    obtain ⟨f, _⟩ := hN dummy
    have hlast :=
      SMTree.AM.sourceLast_le_terminalLevel
        H (by omega : 0 < D + 1) f.1
    rw [f.2] at hlast
    omega

  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hDN
  subst N
  refine ⟨k, ?_⟩
  intro colouring

  let shapeColour :
      SMTree.AM.At H 0 (a + 1) (D + k) → Fin colours :=
    fun q => colouring (E.toSubspace q)

  obtain ⟨f, hf⟩ := hN shapeColour
  let W : FixedSubspace D (D + k) := E.toSubspace f
  let g₀ :
      SMTree.AM.At H 0 (a + 1) (D + 1 - 1) :=
    Classical.choice (E.coordinate_nonempty haD)
  let c : Fin colours :=
    shapeColour
      (SMTree.exactComp H
        (by omega : 0 < D + 1)
        (by omega : 0 < a + 1)
        f g₀)

  refine ⟨W, c, ?_⟩
  intro P hPW
  obtain ⟨g, hg⟩ := E.factor haD f P hPW
  have hmono := hf g g₀
  change
    colouring
        (E.toSubspace
          (SMTree.exactComp H
            (by omega : 0 < D + 1)
            (by omega : 0 < a + 1)
            f g)) =
      colouring
        (E.toSubspace
          (SMTree.exactComp H
            (by omega : 0 < D + 1)
            (by omega : 0 < a + 1)
            f g₀)) at hmono
  rw [hg] at hmono
  exact hmono

end SuccessorTree.NonPrecompact
