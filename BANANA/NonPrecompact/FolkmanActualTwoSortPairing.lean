import BANANA.NonPrecompact.FolkmanPivotCrossIdentities
import BANANA.NonPrecompact.FolkmanPairingFromRetractions

/-!
# An actual pairing on the finite two-sorted Folkman ring amalgam

The pivot choices and retractions refer to the *actual*
compatible-pair-plus-private-point atom grids, not abstract split
linear coordinates.  The pairing here is defined directly on their
finite-subset Boolean-ring carriers.

The first two theorems establish preservation of the complete source
pairings under the already verified two-sort Boolean-ring embeddings.
The construction is stated with a common-base pairing βA and explicit
compatibility on both source sides.

The final class-level strong-amalgamation package additionally needs
biadditivity of this concrete pairing; that is kept as a separate
proof obligation, not silently inferred from ring-map preservation.
-/

namespace SuccessorTree.NonPrecompact
namespace FolkmanFiniteTwoSortAtomDiagram

variable {AL BL CL AR BR CR : Type*}
variable [Fintype AL] [Fintype BL] [Fintype CL]
variable [Fintype AR] [Fintype BR] [Fintype CR]

/-- Extend arbitrary compatible source pairings to the **actual**
two-sorted finite Boolean-ring atom-grid amalgam using pivot
retractions; private outside atoms remain present. -/
noncomputable def pairingByPivots
    (D : FolkmanFiniteTwoSortAtomDiagram AL BL CL AR BR CR)
    (βA : Finset AL → Finset AR → F2)
    (βB : Finset BL → Finset BR → F2)
    (βC : Finset CL → Finset CR → F2) :
    Finset (FolkmanAtomAmalgam D.fL D.gL) →
      Finset (FolkmanAtomAmalgam D.fR D.gR) → F2 :=
  let PL := folkmanChooseAtomPivots D.fL D.gL D.hfL D.hgL
  let PR := folkmanChooseAtomPivots D.fR D.gR D.hfR D.hgR
  folkmanPairingFromRetractions βA βB βC
    (folkmanPivotBaseRetract D.fL D.gL PL)
    (folkmanPivotBaseRetract D.fR D.gR PR)
    (folkmanPivotLeftRetract D.fL D.gL PL)
    (folkmanPivotLeftRetract D.fR D.gR PR)
    (folkmanPivotRightRetract D.fL D.gL PL)
    (folkmanPivotRightRetract D.fR D.gR PR)

/-- The actual pairing agrees with the full B-source pairing,
including all vectors, not merely atoms or representatives. -/
theorem pairingByPivots_embedB
    (D : FolkmanFiniteTwoSortAtomDiagram AL BL CL AR BR CR)
    (βA : Finset AL → Finset AR → F2)
    (βB : Finset BL → Finset BR → F2)
    (βC : Finset CL → Finset CR → F2)
    (hcommonC : ∀ a r,
      βC (folkmanFinsetBaseRight D.gL a)
        (folkmanFinsetBaseRight D.gR r) = βA a r)
    (x : Finset BL) (y : Finset BR) :
    D.pairingByPivots βA βB βC
      (D.embedB (x, y)).1 (D.embedB (x, y)).2 = βB x y := by
  classical
  let PL := folkmanChooseAtomPivots D.fL D.gL D.hfL D.hgL
  let PR := folkmanChooseAtomPivots D.fR D.gR D.hfR D.hgR
  change folkmanPairingFromRetractions βA βB βC
    (folkmanPivotBaseRetract D.fL D.gL PL)
    (folkmanPivotBaseRetract D.fR D.gR PR)
    (folkmanPivotLeftRetract D.fL D.gL PL)
    (folkmanPivotLeftRetract D.fR D.gR PR)
    (folkmanPivotRightRetract D.fL D.gL PL)
    (folkmanPivotRightRetract D.fR D.gR PR)
    (folkmanFinsetLeftMap D.fL D.gL x)
    (folkmanFinsetLeftMap D.fR D.gR y) = βB x y
  exact folkmanPairingFromRetractions_left βA βB βC
    (folkmanPivotBaseRetract D.fL D.gL PL)
    (folkmanPivotBaseRetract D.fR D.gR PR)
    (folkmanPivotLeftRetract D.fL D.gL PL)
    (folkmanPivotLeftRetract D.fR D.gR PR)
    (folkmanPivotRightRetract D.fL D.gL PL)
    (folkmanPivotRightRetract D.fR D.gR PR)
    (folkmanFinsetLeftMap D.fL D.gL)
    (folkmanFinsetLeftMap D.fR D.gR)
    (folkmanFinsetBaseRight D.gL)
    (folkmanFinsetBaseRight D.gR)
    (folkmanPivotLeftRetract_leftMap D.fL D.gL PL)
    (folkmanPivotLeftRetract_leftMap D.fR D.gR PR)
    (folkmanPivotRightRetract_leftMap D.fL D.gL PL)
    (folkmanPivotRightRetract_leftMap D.fR D.gR PR)
    hcommonC x y

/-- The actual pairing also recovers the full C-source pairing. -/
theorem pairingByPivots_embedC
    (D : FolkmanFiniteTwoSortAtomDiagram AL BL CL AR BR CR)
    (βA : Finset AL → Finset AR → F2)
    (βB : Finset BL → Finset BR → F2)
    (βC : Finset CL → Finset CR → F2)
    (hcommonB : ∀ a r,
      βB (folkmanFinsetBaseLeft D.fL a)
        (folkmanFinsetBaseLeft D.fR r) = βA a r)
    (x : Finset CL) (y : Finset CR) :
    D.pairingByPivots βA βB βC
      (D.embedC (x, y)).1 (D.embedC (x, y)).2 = βC x y := by
  classical
  let PL := folkmanChooseAtomPivots D.fL D.gL D.hfL D.hgL
  let PR := folkmanChooseAtomPivots D.fR D.gR D.hfR D.hgR
  change folkmanPairingFromRetractions βA βB βC
    (folkmanPivotBaseRetract D.fL D.gL PL)
    (folkmanPivotBaseRetract D.fR D.gR PR)
    (folkmanPivotLeftRetract D.fL D.gL PL)
    (folkmanPivotLeftRetract D.fR D.gR PR)
    (folkmanPivotRightRetract D.fL D.gL PL)
    (folkmanPivotRightRetract D.fR D.gR PR)
    (folkmanFinsetRightMap D.fL D.gL x)
    (folkmanFinsetRightMap D.fR D.gR y) = βC x y
  exact folkmanPairingFromRetractions_right βA βB βC
    (folkmanPivotBaseRetract D.fL D.gL PL)
    (folkmanPivotBaseRetract D.fR D.gR PR)
    (folkmanPivotLeftRetract D.fL D.gL PL)
    (folkmanPivotLeftRetract D.fR D.gR PR)
    (folkmanPivotRightRetract D.fL D.gL PL)
    (folkmanPivotRightRetract D.fR D.gR PR)
    (folkmanFinsetRightMap D.fL D.gL)
    (folkmanFinsetRightMap D.fR D.gR)
    (folkmanFinsetBaseLeft D.fL)
    (folkmanFinsetBaseLeft D.fR)
    (folkmanPivotRightRetract_rightMap D.fL D.gL PL)
    (folkmanPivotRightRetract_rightMap D.fR D.gR PR)
    (folkmanPivotLeftRetract_rightMap D.fL D.gL PL)
    (folkmanPivotLeftRetract_rightMap D.fR D.gR PR)
    hcommonB x y

end FolkmanFiniteTwoSortAtomDiagram
end SuccessorTree.NonPrecompact
