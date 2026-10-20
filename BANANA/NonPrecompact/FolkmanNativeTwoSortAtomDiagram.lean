import BANANA.NonPrecompact.FolkmanNativeNonUnitalRingOwners
import BANANA.NonPrecompact.FolkmanFiniteStrongAmalgamPairing

/-!
# Canonical atom diagram for arbitrary finite two-sort Folkman embeddings

The circulation strong amalgamation starts with two embeddings of a
common pair of finite Boolean rings. Neither side is required to
preserve the ring unit.  The native NonUnitalRingHom partial-owner
theorem is applied independently to the left and right ring sorts,
giving exactly the four Option-valued atom maps required by the
kernel-checked concrete two-sort atom-grid strong amalgam.

The result retains the *exact* powerset representation of each
of the four input embeddings. No pairing transport is claimed here;
that is the next independent theorem.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- The canonical finite atom code of a native non-unital ring map. -/
noncomputable def folkmanNativeRingAtomMap
    {R S : Type*}
    [BooleanRing R] [Fintype R]
    [BooleanRing S] [Fintype S]
    (f : R →ₙ+* S) :
    Finset (PrebananaAbstractAtoms (AsBoolAlg R)) →
      Finset (PrebananaAbstractAtoms (AsBoolAlg S)) :=
  prebananaAbstractPowersetMap
    (fun x : AsBoolAlg R => toBoolAlg (f (ofBoolAlg x)))

/-- All four non-unital finite Boolean-ring embeddings of a
two-sort amalgamation diagram simultaneously admit a genuine
FolkmanFiniteTwoSortAtomDiagram.  No top preservation is assumed. -/
theorem folkmanNativeTwoSort_exists_atomDiagram
    {AL BL CL AR BR CR : Type*}
    [BooleanRing AL] [Fintype AL]
    [BooleanRing BL] [Fintype BL]
    [BooleanRing CL] [Fintype CL]
    [BooleanRing AR] [Fintype AR]
    [BooleanRing BR] [Fintype BR]
    [BooleanRing CR] [Fintype CR]
    (fL : AL →ₙ+* BL) (gL : AL →ₙ+* CL)
    (fR : AR →ₙ+* BR) (gR : AR →ₙ+* CR)
    (hfL : Function.Injective fL)
    (hgL : Function.Injective gL)
    (hfR : Function.Injective fR)
    (hgR : Function.Injective gR) :
    ∃ D : FolkmanFiniteTwoSortAtomDiagram
        (PrebananaAbstractAtoms (AsBoolAlg AL))
        (PrebananaAbstractAtoms (AsBoolAlg BL))
        (PrebananaAbstractAtoms (AsBoolAlg CL))
        (PrebananaAbstractAtoms (AsBoolAlg AR))
        (PrebananaAbstractAtoms (AsBoolAlg BR))
        (PrebananaAbstractAtoms (AsBoolAlg CR)),
      (∀ s : Finset (PrebananaAbstractAtoms (AsBoolAlg AL)),
        folkmanNativeRingAtomMap fL s =
          Finset.univ.filter
            (fun b => ∃ a ∈ s, D.fL b = some a)) ∧
      (∀ s : Finset (PrebananaAbstractAtoms (AsBoolAlg AL)),
        folkmanNativeRingAtomMap gL s =
          Finset.univ.filter
            (fun c => ∃ a ∈ s, D.gL c = some a)) ∧
      (∀ s : Finset (PrebananaAbstractAtoms (AsBoolAlg AR)),
        folkmanNativeRingAtomMap fR s =
          Finset.univ.filter
            (fun b => ∃ a ∈ s, D.fR b = some a)) ∧
      (∀ s : Finset (PrebananaAbstractAtoms (AsBoolAlg AR)),
        folkmanNativeRingAtomMap gR s =
          Finset.univ.filter
            (fun c => ∃ a ∈ s, D.gR c = some a)) := by
  classical
  obtain ⟨pFL, hpFL, hmapFL⟩ :=
    folkmanNonUnitalRingEmbedding_exists_partialAtomOwner fL hfL
  obtain ⟨pGL, hpGL, hmapGL⟩ :=
    folkmanNonUnitalRingEmbedding_exists_partialAtomOwner gL hgL
  obtain ⟨pFR, hpFR, hmapFR⟩ :=
    folkmanNonUnitalRingEmbedding_exists_partialAtomOwner fR hfR
  obtain ⟨pGR, hpGR, hmapGR⟩ :=
    folkmanNonUnitalRingEmbedding_exists_partialAtomOwner gR hgR
  let D : FolkmanFiniteTwoSortAtomDiagram
      (PrebananaAbstractAtoms (AsBoolAlg AL))
      (PrebananaAbstractAtoms (AsBoolAlg BL))
      (PrebananaAbstractAtoms (AsBoolAlg CL))
      (PrebananaAbstractAtoms (AsBoolAlg AR))
      (PrebananaAbstractAtoms (AsBoolAlg BR))
      (PrebananaAbstractAtoms (AsBoolAlg CR)) := {
    fL := pFL
    gL := pGL
    fR := pFR
    gR := pGR
    hfL := hpFL
    hgL := hpGL
    hfR := hpFR
    hgR := hpGR
  }
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · exact hmapFL
  · exact hmapGL
  · exact hmapFR
  · exact hmapGR

end SuccessorTree.NonPrecompact
