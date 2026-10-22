import BANANA.NonPrecompact.FolkmanNativePairingTransport

/-!
# Compatibility of native Folkman pairings under atom coordinates

An isometry of two finite non-unital Boolean-ring sorts remains an
isometry after transporting the two pairings to finite atom subsets.
This supplies the common-base compatibility hypothesis in the already
verified finite-atom strong-amalgamation theorem.

The result applies to non-unital maps without preserving the top
element and includes the one-element zero ring.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

-- This instance is required while elaborating the theorem statement,
-- before entering the proof, by prebananaAbstractPowersetMap.
local instance folkmanAsBoolAlgFiniteForPairingCompatibility
    (γ : Type*) [Fintype γ] : Fintype (AsBoolAlg γ) :=
  Fintype.ofEquiv γ toBoolAlg

/-- Native compatibility of a bilinear pairing is preserved when both
sorts and both embeddings are expressed in canonical atom coordinates. -/
theorem folkmanNativeTransportPairing_compatible
    {AL BL AR BR : Type*}
    [BooleanRing AL] [Fintype AL]
    [BooleanRing BL] [Fintype BL]
    [BooleanRing AR] [Fintype AR]
    [BooleanRing BR] [Fintype BR]
    (fL : AL →ₙ+* BL) (fR : AR →ₙ+* BR)
    (γA : AL → AR → F2) (γB : BL → BR → F2)
    (hcompat : ∀ a r, γB (fL a) (fR r) = γA a r)
    (s : Finset (PrebananaAbstractAtoms (AsBoolAlg AL)))
    (t : Finset (PrebananaAbstractAtoms (AsBoolAlg AR))) :
    folkmanNativeTransportPairing γB
      (prebananaAbstractPowersetMap
        (fun x : AsBoolAlg AL => toBoolAlg (fL (ofBoolAlg x))) s)
      (prebananaAbstractPowersetMap
        (fun x : AsBoolAlg AR => toBoolAlg (fR (ofBoolAlg x))) t) =
      folkmanNativeTransportPairing γA s t := by
  classical
  rw [← folkmanNativeRingAtomEquiv_map fL s,
      ← folkmanNativeRingAtomEquiv_map fR t]
  simpa only [folkmanNativeTransportPairing, Equiv.symm_apply_apply] using
    (hcompat ((folkmanNativeRingAtomEquiv AL).symm s)
      ((folkmanNativeRingAtomEquiv AR).symm t))

end SuccessorTree.NonPrecompact
