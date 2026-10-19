import BANANA.NonPrecompact.FolkmanActualTwoSortPairing

/-!
# Biadditivity of the concrete Folkman pivot pairing

Given additive F₂-pairings on the three source ring diagrams,
the pairing constructed on the actual two-sort atom-grid amalgam
is additive in each argument. This is a consequence of the
symmetric-difference preservation of all three pivot retractions.

Both complete source-pairing restrictions then follow from the
separate actual-ring transport theorems.

This file does not use vector-space complements. It includes empty
atom sorts and non-unital embeddings with private outside atoms.
-/

namespace SuccessorTree.NonPrecompact
namespace FolkmanFiniteTwoSortAtomDiagram

variable {AL BL CL AR BR CR : Type*}
variable [Fintype AL] [Fintype BL] [Fintype CL]
variable [Fintype AR] [Fintype BR] [Fintype CR]

/-- The explicit actual-ring pairing is additive in its left argument. -/
theorem pairingByPivots_add_left
    (D : FolkmanFiniteTwoSortAtomDiagram AL BL CL AR BR CR)
    (βA : Finset AL → Finset AR → F2)
    (βB : Finset BL → Finset BR → F2)
    (βC : Finset CL → Finset CR → F2)
    (hA : ∀ a a' r,
      βA (symmDiff a a') r = βA a r + βA a' r)
    (hB : ∀ b b' r,
      βB (symmDiff b b') r = βB b r + βB b' r)
    (hC : ∀ c c' r,
      βC (symmDiff c c') r = βC c r + βC c' r)
    (x x' : Finset (FolkmanAtomAmalgam D.fL D.gL))
    (y : Finset (FolkmanAtomAmalgam D.fR D.gR)) :
    D.pairingByPivots βA βB βC (symmDiff x x') y =
      D.pairingByPivots βA βB βC x y +
        D.pairingByPivots βA βB βC x' y := by
  classical
  simp only [pairingByPivots, folkmanPairingFromRetractions,
    folkmanPivotBaseRetract_symmDiff,
    folkmanPivotLeftRetract_symmDiff,
    folkmanPivotRightRetract_symmDiff,
    hA, hB, hC]
  abel

/-- The explicit actual-ring pairing is additive in its right argument. -/
theorem pairingByPivots_add_right
    (D : FolkmanFiniteTwoSortAtomDiagram AL BL CL AR BR CR)
    (βA : Finset AL → Finset AR → F2)
    (βB : Finset BL → Finset BR → F2)
    (βC : Finset CL → Finset CR → F2)
    (hA : ∀ a r r',
      βA a (symmDiff r r') = βA a r + βA a r')
    (hB : ∀ b r r',
      βB b (symmDiff r r') = βB b r + βB b r')
    (hC : ∀ c r r',
      βC c (symmDiff r r') = βC c r + βC c r')
    (x : Finset (FolkmanAtomAmalgam D.fL D.gL))
    (y y' : Finset (FolkmanAtomAmalgam D.fR D.gR)) :
    D.pairingByPivots βA βB βC x (symmDiff y y') =
      D.pairingByPivots βA βB βC x y +
        D.pairingByPivots βA βB βC x y' := by
  classical
  simp only [pairingByPivots, folkmanPairingFromRetractions,
    folkmanPivotBaseRetract_symmDiff,
    folkmanPivotLeftRetract_symmDiff,
    folkmanPivotRightRetract_symmDiff,
    hA, hB, hC]
  abel

/-- Complete concrete strong-amalgam pairing certificate.
The non-unital Boolean-ring embeddings and their strong image
intersection are proved independently in FolkmanFiniteTwoSortRingDiagram;
this theorem supplies the remaining F₂-pairing part. -/
theorem exists_actual_compatible_pairing
    (D : FolkmanFiniteTwoSortAtomDiagram AL BL CL AR BR CR)
    (βA : Finset AL → Finset AR → F2)
    (βB : Finset BL → Finset BR → F2)
    (βC : Finset CL → Finset CR → F2)
    (hAleft : ∀ a a' r,
      βA (symmDiff a a') r = βA a r + βA a' r)
    (hBleft : ∀ b b' r,
      βB (symmDiff b b') r = βB b r + βB b' r)
    (hCleft : ∀ c c' r,
      βC (symmDiff c c') r = βC c r + βC c' r)
    (hAright : ∀ a r r',
      βA a (symmDiff r r') = βA a r + βA a r')
    (hBright : ∀ b r r',
      βB b (symmDiff r r') = βB b r + βB b r')
    (hCright : ∀ c r r',
      βC c (symmDiff r r') = βC c r + βC c r')
    (hcommonB : ∀ a r,
      βB (folkmanFinsetBaseLeft D.fL a)
        (folkmanFinsetBaseLeft D.fR r) = βA a r)
    (hcommonC : ∀ a r,
      βC (folkmanFinsetBaseRight D.gL a)
        (folkmanFinsetBaseRight D.gR r) = βA a r) :
    ∃ βD :
      Finset (FolkmanAtomAmalgam D.fL D.gL) →
      Finset (FolkmanAtomAmalgam D.fR D.gR) → F2,
      (∀ x x' y, βD (symmDiff x x') y =
        βD x y + βD x' y) ∧
      (∀ x y y', βD x (symmDiff y y') =
        βD x y + βD x y') ∧
      (∀ x y, βD (D.embedB (x,y)).1
        (D.embedB (x,y)).2 = βB x y) ∧
      (∀ x y, βD (D.embedC (x,y)).1
        (D.embedC (x,y)).2 = βC x y) := by
  classical
  refine ⟨D.pairingByPivots βA βB βC, ?_, ?_, ?_, ?_⟩
  · exact D.pairingByPivots_add_left βA βB βC
      hAleft hBleft hCleft
  · exact D.pairingByPivots_add_right βA βB βC
      hAright hBright hCright
  · intro x y
    exact D.pairingByPivots_embedB βA βB βC hcommonC x y
  · intro x y
    exact D.pairingByPivots_embedC βA βB βC hcommonB x y

end FolkmanFiniteTwoSortAtomDiagram
end SuccessorTree.NonPrecompact
