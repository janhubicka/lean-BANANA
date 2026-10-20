import BANANA.NonPrecompact.FolkmanNativeNonUnitalRingOwners
import BANANA.NonPrecompact.FolkmanFiniteTwoSortRingDiagram

/-!
# Four native non-unital embeddings give the actual Folkman atom diagram

This is the remaining simultaneous-object interface between arbitrary
finite Boolean-ring embedding diagrams and the checked two-sorted
atom-grid construction.

Each source ring is represented by the atoms of its associated
Boolean algebra. A native non-unital Boolean-ring embedding produces
an Option-valued owner map in the reverse direction. The four owner
maps have nonempty fibres and reconstruct each original embedding
exactly on finite atom supports.

This statement packages those four maps into one concrete
FolkmanFiniteTwoSortAtomDiagram; it does NOT yet claim that the
original bilinear pairings are transported, or that the class-level
Fraïssé theorem has been formally completed.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

-- Finiteness is transported from a native Boolean ring to its
-- associated Boolean algebra; no preservation of top is implied.
local instance folkmanAsBoolAlgFiniteForDiagram
    (γ : Type*) [Fintype γ] : Fintype (AsBoolAlg γ) :=
  Fintype.ofEquiv γ toBoolAlg

/-- The four native ring injections in a two-sorted amalgamation
diagram yield a common finite atom-owner diagram, with exact
reconstruction of each injection on the six finite atom carriers.

No ring homomorphism is assumed to preserve the greatest element,
and zero rings are permitted on either sort. -/
theorem folkmanNativeTwoSort_exists_atomDiagram
    {AL BL CL AR BR CR : Type*}
    [BooleanRing AL] [BooleanRing BL] [BooleanRing CL]
    [BooleanRing AR] [BooleanRing BR] [BooleanRing CR]
    [Fintype AL] [Fintype BL] [Fintype CL]
    [Fintype AR] [Fintype BR] [Fintype CR]
    (fBL : AL →ₙ+* BL) (gCL : AL →ₙ+* CL)
    (fBR : AR →ₙ+* BR) (gCR : AR →ₙ+* CR)
    (hfBL : Function.Injective fBL)
    (hgCL : Function.Injective gCL)
    (hfBR : Function.Injective fBR)
    (hgCR : Function.Injective gCR) :
    ∃ D : FolkmanFiniteTwoSortAtomDiagram
        (PrebananaAbstractAtoms (AsBoolAlg AL))
        (PrebananaAbstractAtoms (AsBoolAlg BL))
        (PrebananaAbstractAtoms (AsBoolAlg CL))
        (PrebananaAbstractAtoms (AsBoolAlg AR))
        (PrebananaAbstractAtoms (AsBoolAlg BR))
        (PrebananaAbstractAtoms (AsBoolAlg CR)),
      (∀ s : Finset (PrebananaAbstractAtoms (AsBoolAlg AL)),
        prebananaAbstractPowersetMap
            (fun x : AsBoolAlg AL => toBoolAlg (fBL (ofBoolAlg x))) s =
          Finset.univ.filter
            (fun b => ∃ a ∈ s, D.fL b = some a)) ∧
      (∀ s : Finset (PrebananaAbstractAtoms (AsBoolAlg AL)),
        prebananaAbstractPowersetMap
            (fun x : AsBoolAlg AL => toBoolAlg (gCL (ofBoolAlg x))) s =
          Finset.univ.filter
            (fun c => ∃ a ∈ s, D.gL c = some a)) ∧
      (∀ s : Finset (PrebananaAbstractAtoms (AsBoolAlg AR)),
        prebananaAbstractPowersetMap
            (fun x : AsBoolAlg AR => toBoolAlg (fBR (ofBoolAlg x))) s =
          Finset.univ.filter
            (fun b => ∃ a ∈ s, D.fR b = some a)) ∧
      (∀ s : Finset (PrebananaAbstractAtoms (AsBoolAlg AR)),
        prebananaAbstractPowersetMap
            (fun x : AsBoolAlg AR => toBoolAlg (gCR (ofBoolAlg x))) s =
          Finset.univ.filter
            (fun c => ∃ a ∈ s, D.gR c = some a)) := by
  classical
  obtain ⟨pBL, hpBL, heBL⟩ :=
    folkmanNonUnitalRingEmbedding_exists_partialAtomOwner fBL hfBL
  obtain ⟨pCL, hpCL, heCL⟩ :=
    folkmanNonUnitalRingEmbedding_exists_partialAtomOwner gCL hgCL
  obtain ⟨pBR, hpBR, heBR⟩ :=
    folkmanNonUnitalRingEmbedding_exists_partialAtomOwner fBR hfBR
  obtain ⟨pCR, hpCR, heCR⟩ :=
    folkmanNonUnitalRingEmbedding_exists_partialAtomOwner gCR hgCR
  exact ⟨{
    fL := pBL
    gL := pCL
    fR := pBR
    gR := pCR
    hfL := hpBL
    hgL := hpCL
    hfR := hpBR
    hgR := hpCR
  }, heBL, heCL, heBR, heCR⟩

end SuccessorTree.NonPrecompact
