import BANANA.NonPrecompact.FolkmanNativeEmbeddings
import BANANA.NonPrecompact.FolkmanIntersectionTransport

/-!
# Exact intersection of embeddings of original native Folkman rings

This combines the canonical atom-coordinate equivalences with the
proved exact common-base intersection of the actual two-sort atom-grid
amalgam.  Unlike the coordinate statement, the conclusion is
formulated on original pairs of finite Boolean rings and uses precisely
the four given non-unital base embeddings.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

local instance folkmanAsBoolAlgFiniteForOriginalIntersection
    (γ : Type*) [Fintype γ] : Fintype (AsBoolAlg γ) :=
  Fintype.ofEquiv γ toBoolAlg

/-- A pair of native finite Boolean rings is equivalent, as a carrier,
to the two finite atom-subset spaces. -/
noncomputable def folkmanNativeTwoSortEquiv
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R] :
    (L × R) ≃
      (Finset (PrebananaAbstractAtoms (AsBoolAlg L)) ×
       Finset (PrebananaAbstractAtoms (AsBoolAlg R))) where
  toFun := folkmanNativeTwoSortCode
  invFun := fun p =>
    ((folkmanNativeRingAtomEquiv L).symm p.1,
     (folkmanNativeRingAtomEquiv R).symm p.2)
  left_inv := by
    intro x
    apply Prod.ext
    · exact (folkmanNativeRingAtomEquiv L).symm_apply_apply x.1
    · exact (folkmanNativeRingAtomEquiv R).symm_apply_apply x.2
  right_inv := by
    intro p
    apply Prod.ext
    · exact (folkmanNativeRingAtomEquiv L).apply_symm_apply p.1
    · exact (folkmanNativeRingAtomEquiv R).apply_symm_apply p.2

variable {AL BL CL AR BR CR : Type*}
variable [BooleanRing AL] [BooleanRing BL] [BooleanRing CL]
variable [BooleanRing AR] [BooleanRing BR] [BooleanRing CR]
variable [Fintype AL] [Fintype BL] [Fintype CL]
variable [Fintype AR] [Fintype BR] [Fintype CR]

variable (D : FolkmanFiniteTwoSortAtomDiagram
  (PrebananaAbstractAtoms (AsBoolAlg AL))
  (PrebananaAbstractAtoms (AsBoolAlg BL))
  (PrebananaAbstractAtoms (AsBoolAlg CL))
  (PrebananaAbstractAtoms (AsBoolAlg AR))
  (PrebananaAbstractAtoms (AsBoolAlg BR))
  (PrebananaAbstractAtoms (AsBoolAlg CR)))

/-- Exact intersection of the two original native-ring images:
equality in the actual amalgam holds precisely when the original
B- and C-side ring pairs come from a common native base element.

The hypotheses connect the four given original embeddings with
the concrete owner maps; no preservation of ring top is used. -/
theorem folkmanNativeEmbed_images_eq_iff_common_base
    (fBL : AL →ₙ+* BL) (gCL : AL →ₙ+* CL)
    (fBR : AR →ₙ+* BR) (gCR : AR →ₙ+* CR)
    (hbaseB : ∀ a : AL × AR,
      D.baseB (folkmanNativeTwoSortCode a) =
        folkmanNativeTwoSortCode (fBL a.1, fBR a.2))
    (hbaseC : ∀ a : AL × AR,
      D.baseC (folkmanNativeTwoSortCode a) =
        folkmanNativeTwoSortCode (gCL a.1, gCR a.2))
    (b : BL × BR) (c : CL × CR) :
    folkmanNativeEmbedB D b = folkmanNativeEmbedC D c ↔
      ∃ a : AL × AR,
        b = (fBL a.1, fBR a.2) ∧
        c = (gCL a.1, gCR a.2) := by
  exact D.images_eq_iff_common_base_of_equivs
    (folkmanNativeTwoSortEquiv (L := AL) (R := AR))
    (folkmanNativeTwoSortEquiv (L := BL) (R := BR))
    (folkmanNativeTwoSortEquiv (L := CL) (R := CR))
    (fun a => (fBL a.1, fBR a.2))
    (fun a => (gCL a.1, gCR a.2))
    hbaseB hbaseC b c

end SuccessorTree.NonPrecompact
