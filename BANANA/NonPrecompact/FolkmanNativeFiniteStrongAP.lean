import BANANA.NonPrecompact.FolkmanNativeStrongAmalgam
import BANANA.NonPrecompact.FolkmanNativeIntersection

/-!
# Finite strong amalgamation for the native Folkman--BANANA language

This packages the previously checked native non-unital Boolean-ring
embeddings, compatible bilinear pairings and exact native-image
intersection into one finite two-sorted strong-amalgamation theorem.

All source objects are arbitrary finite Boolean rings (including zero
rings), and the four embeddings preserve zero, addition and
multiplication, but are not required to preserve the greatest element.
The two amalgam carriers are the actual finite atom-grid rings.

The finite Fraisse-class properties (heredity, joint embedding,
countability of isomorphism types) and the countable limit are
separate obligations. In particular this theorem does not assert
that an arbitrary infinite structure has been constructed.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff

local instance folkmanAsBoolAlgFiniteForFullNativeAP
    (α : Type*) [Fintype α] : Fintype (AsBoolAlg α) :=
  Fintype.ofEquiv α toBoolAlg

/-- An arbitrary compatible native finite two-sorted Folkman diagram
has a pairing-preserving *strong* amalgam. The conclusion verifies the
actual native source embeddings on the original ring elements, all
Boolean-ring operations, commutation over the base, and exact
common-base intersection, not only equalities on atom representatives. -/
theorem folkmanNativeTwoSort_exists_finiteStrongAP
    {AL BL CL AR BR CR : Type*}
    [BooleanRing AL] [Fintype AL]
    [BooleanRing BL] [Fintype BL]
    [BooleanRing CL] [Fintype CL]
    [BooleanRing AR] [Fintype AR]
    [BooleanRing BR] [Fintype BR]
    [BooleanRing CR] [Fintype CR]
    (fBL : AL →ₙ+* BL) (gCL : AL →ₙ+* CL)
    (fBR : AR →ₙ+* BR) (gCR : AR →ₙ+* CR)
    (hfBL : Function.Injective fBL)
    (hgCL : Function.Injective gCL)
    (hfBR : Function.Injective fBR)
    (hgCR : Function.Injective gCR)
    (γA : AL → AR → F2)
    (γB : BL → BR → F2)
    (γC : CL → CR → F2)
    (hAleft : ∀ x x' y, γA (x + x') y = γA x y + γA x' y)
    (hBleft : ∀ x x' y, γB (x + x') y = γB x y + γB x' y)
    (hCleft : ∀ x x' y, γC (x + x') y = γC x y + γC x' y)
    (hAright : ∀ x y y', γA x (y + y') = γA x y + γA x y')
    (hBright : ∀ x y y', γB x (y + y') = γB x y + γB x y')
    (hCright : ∀ x y y', γC x (y + y') = γC x y + γC x y')
    (hcommonB : ∀ a r, γB (fBL a) (fBR r) = γA a r)
    (hcommonC : ∀ a r, γC (gCL a) (gCR r) = γA a r) :
    ∃ D : FolkmanFiniteTwoSortAtomDiagram
        (PrebananaAbstractAtoms (AsBoolAlg AL))
        (PrebananaAbstractAtoms (AsBoolAlg BL))
        (PrebananaAbstractAtoms (AsBoolAlg CL))
        (PrebananaAbstractAtoms (AsBoolAlg AR))
        (PrebananaAbstractAtoms (AsBoolAlg BR))
        (PrebananaAbstractAtoms (AsBoolAlg CR)),
      ∃ βD : Finset (FolkmanAtomAmalgam D.fL D.gL) →
          Finset (FolkmanAtomAmalgam D.fR D.gR) → F2,
        (∀ u u' v, βD (symmDiff u u') v =
          βD u v + βD u' v) ∧
        (∀ u v v', βD u (symmDiff v v') =
          βD u v + βD u v') ∧
        Function.Injective (folkmanNativeEmbedB D) ∧
        Function.Injective (folkmanNativeEmbedC D) ∧
        folkmanNativeEmbedB D ((0 : BL), (0 : BR)) = (∅, ∅) ∧
        folkmanNativeEmbedC D ((0 : CL), (0 : CR)) = (∅, ∅) ∧
        (∀ x y : BL × BR,
          folkmanNativeEmbedB D (x.1 + y.1, x.2 + y.2) =
            folkmanTwoSortSymmDiff
              (folkmanNativeEmbedB D x) (folkmanNativeEmbedB D y)) ∧
        (∀ x y : CL × CR,
          folkmanNativeEmbedC D (x.1 + y.1, x.2 + y.2) =
            folkmanTwoSortSymmDiff
              (folkmanNativeEmbedC D x) (folkmanNativeEmbedC D y)) ∧
        (∀ x y : BL × BR,
          folkmanNativeEmbedB D (x.1 * y.1, x.2 * y.2) =
            folkmanTwoSortInter
              (folkmanNativeEmbedB D x) (folkmanNativeEmbedB D y)) ∧
        (∀ x y : CL × CR,
          folkmanNativeEmbedC D (x.1 * y.1, x.2 * y.2) =
            folkmanTwoSortInter
              (folkmanNativeEmbedC D x) (folkmanNativeEmbedC D y)) ∧
        (∀ b : BL × BR,
          βD (folkmanNativeEmbedB D b).1
             (folkmanNativeEmbedB D b).2 = γB b.1 b.2) ∧
        (∀ c : CL × CR,
          βD (folkmanNativeEmbedC D c).1
             (folkmanNativeEmbedC D c).2 = γC c.1 c.2) ∧
        (∀ a : AL × AR,
          folkmanNativeEmbedB D (fBL a.1, fBR a.2) =
            folkmanNativeEmbedC D (gCL a.1, gCR a.2)) ∧
        (∀ b : BL × BR, ∀ c : CL × CR,
          folkmanNativeEmbedB D b = folkmanNativeEmbedC D c ↔
            ∃ a : AL × AR,
              b = (fBL a.1, fBR a.2) ∧
              c = (gCL a.1, gCR a.2)) := by
  classical
  obtain ⟨D, βD, hleft, hright, hBpair, hCpair, _,
    hbaseB, hbaseC⟩ :=
    folkmanNativeTwoSort_exists_strongAmalgamPairing
      fBL gCL fBR gCR hfBL hgCL hfBR hgCR
      γA γB γC hAleft hBleft hCleft
      hAright hBright hCright hcommonB hcommonC
  have hbcode (a : AL × AR) :
      D.baseB (folkmanNativeTwoSortCode a) =
        folkmanNativeTwoSortCode (fBL a.1, fBR a.2) := by
    simpa only [folkmanNativeTwoSortCode] using hbaseB a
  have hccode (a : AL × AR) :
      D.baseC (folkmanNativeTwoSortCode a) =
        folkmanNativeTwoSortCode (gCL a.1, gCR a.2) := by
    simpa only [folkmanNativeTwoSortCode] using hbaseC a
  have hinter (b : BL × BR) (c : CL × CR) :
      folkmanNativeEmbedB D b = folkmanNativeEmbedC D c ↔
        ∃ a : AL × AR,
          b = (fBL a.1, fBR a.2) ∧
          c = (gCL a.1, gCR a.2) :=
    folkmanNativeEmbed_images_eq_iff_common_base D
      fBL gCL fBR gCR hbcode hccode b c
  refine ⟨D, βD, ?_, ?_, folkmanNativeEmbedB_injective D,
    folkmanNativeEmbedC_injective D,
    folkmanNativeEmbedB_zero D, folkmanNativeEmbedC_zero D,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hinter⟩
  · intro u u' v
    convert hleft u u' v using 1
      <;> first | rfl |
        (congr 1; ext z; simp only [Finset.mem_symmDiff])
  · intro u v v'
    convert hright u v v' using 1
      <;> first | rfl |
        (congr 1; ext z; simp only [Finset.mem_symmDiff])
  · intro x y
    exact folkmanNativeEmbedB_add D x y
  · intro x y
    exact folkmanNativeEmbedC_add D x y
  · intro x y
    exact folkmanNativeEmbedB_mul D x y
  · intro x y
    exact folkmanNativeEmbedC_mul D x y
  · intro b
    simpa only [folkmanNativeEmbedB, folkmanNativeTwoSortCode] using
      hBpair b.1 b.2
  · intro c
    simpa only [folkmanNativeEmbedC, folkmanNativeTwoSortCode] using
      hCpair c.1 c.2
  · intro a
    exact (hinter _ _).2 ⟨a, rfl, rfl⟩

end SuccessorTree.NonPrecompact
