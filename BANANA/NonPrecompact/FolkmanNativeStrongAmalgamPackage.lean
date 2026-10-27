import BANANA.NonPrecompact.FolkmanNativeStrongAmalgam
import BANANA.NonPrecompact.FolkmanNativeIntersection

/-!
# Finite Folkman strong amalgamation in the original two-sorted language

The previous six-ring theorem constructs the actual two-sort
atom-grid amalgam and extends both native F₂-bilinear pairings.
The embedding and intersection lemmas are independently proved
on the original Boolean-ring carriers.

This file packages those results into a single witness, retaining
the ring operations, both source pairings, agreement on the base
and the exact strong intersection of the source images.

No embedding is assumed to preserve the multiplicative unit.
The one-element zero ring is allowed in every sort.  The separate
Fraïssé-class bookkeeping (heredity, joint embedding, finite
isomorphism types and unboundedness) is not asserted here.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff

local instance folkmanAsBoolAlgFiniteForStrongAPPackage
    (γ : Type*) [Fintype γ] : Fintype (AsBoolAlg γ) :=
  Fintype.ofEquiv γ toBoolAlg

variable {AL BL CL AR BR CR : Type*}
variable [BooleanRing AL] [Fintype AL]
variable [BooleanRing BL] [Fintype BL]
variable [BooleanRing CL] [Fintype CL]
variable [BooleanRing AR] [Fintype AR]
variable [BooleanRing BR] [Fintype BR]
variable [BooleanRing CR] [Fintype CR]

/-- A complete concrete strong-amalgamation witness, formulated on the
original finite two-sort Boolean-ring carriers rather than only on
their atom-subset coordinate spaces. -/
structure FolkmanNativeStrongAmalgamCertificate
    (fBL : AL →ₙ+* BL) (gCL : AL →ₙ+* CL)
    (fBR : AR →ₙ+* BR) (gCR : AR →ₙ+* CR)
    (γB : BL → BR → F2) (γC : CL → CR → F2) where
  diagram : FolkmanFiniteTwoSortAtomDiagram
    (PrebananaAbstractAtoms (AsBoolAlg AL))
    (PrebananaAbstractAtoms (AsBoolAlg BL))
    (PrebananaAbstractAtoms (AsBoolAlg CL))
    (PrebananaAbstractAtoms (AsBoolAlg AR))
    (PrebananaAbstractAtoms (AsBoolAlg BR))
    (PrebananaAbstractAtoms (AsBoolAlg CR))
  pairing : Finset (FolkmanAtomAmalgam diagram.fL diagram.gL) →
    Finset (FolkmanAtomAmalgam diagram.fR diagram.gR) → F2
  additive_left : ∀ x x' y,
    pairing (symmDiff x x') y = pairing x y + pairing x' y
  additive_right : ∀ x y y',
    pairing x (symmDiff y y') = pairing x y + pairing x y'
  injective_B : Function.Injective (folkmanNativeEmbedB diagram)
  injective_C : Function.Injective (folkmanNativeEmbedC diagram)
  zero_B : folkmanNativeEmbedB diagram ((0 : BL), (0 : BR)) = (∅, ∅)
  zero_C : folkmanNativeEmbedC diagram ((0 : CL), (0 : CR)) = (∅, ∅)
  add_B : ∀ x y : BL × BR,
    folkmanNativeEmbedB diagram (x.1 + y.1, x.2 + y.2) =
      folkmanTwoSortSymmDiff (folkmanNativeEmbedB diagram x)
        (folkmanNativeEmbedB diagram y)
  add_C : ∀ x y : CL × CR,
    folkmanNativeEmbedC diagram (x.1 + y.1, x.2 + y.2) =
      folkmanTwoSortSymmDiff (folkmanNativeEmbedC diagram x)
        (folkmanNativeEmbedC diagram y)
  mul_B : ∀ x y : BL × BR,
    folkmanNativeEmbedB diagram (x.1 * y.1, x.2 * y.2) =
      folkmanTwoSortInter (folkmanNativeEmbedB diagram x)
        (folkmanNativeEmbedB diagram y)
  mul_C : ∀ x y : CL × CR,
    folkmanNativeEmbedC diagram (x.1 * y.1, x.2 * y.2) =
      folkmanTwoSortInter (folkmanNativeEmbedC diagram x)
        (folkmanNativeEmbedC diagram y)
  preserves_pairing_B : ∀ x : BL, ∀ y : BR,
    pairing (folkmanNativeEmbedB diagram (x, y)).1
      (folkmanNativeEmbedB diagram (x, y)).2 = γB x y
  preserves_pairing_C : ∀ x : CL, ∀ y : CR,
    pairing (folkmanNativeEmbedC diagram (x, y)).1
      (folkmanNativeEmbedC diagram (x, y)).2 = γC x y
  base_commutes : ∀ a : AL × AR,
    folkmanNativeEmbedB diagram (fBL a.1, fBR a.2) =
      folkmanNativeEmbedC diagram (gCL a.1, gCR a.2)
  strong_intersection : ∀ b : BL × BR, ∀ c : CL × CR,
    folkmanNativeEmbedB diagram b = folkmanNativeEmbedC diagram c ↔
      ∃ a : AL × AR,
        b = (fBL a.1, fBR a.2) ∧
        c = (gCL a.1, gCR a.2)

/-- Every compatible diagram of finite two-sort native Boolean rings
and F₂-bilinear pairings admits strong amalgamation preserving the
entire original language.  The conclusion packages the already
verified ring, pairing and exact-intersection maps. -/
theorem folkmanNative_exists_language_strong_amalgam
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
    Nonempty (FolkmanNativeStrongAmalgamCertificate
      fBL gCL fBR gCR γB γC) := by
  classical
  obtain ⟨D, βD, hleft, hright, hpB, hpC, _, hbaseB, hbaseC⟩ :=
    folkmanNativeTwoSort_exists_strongAmalgamPairing
      fBL gCL fBR gCR hfBL hgCL hfBR hgCR
      γA γB γC
      hAleft hBleft hCleft hAright hBright hCright
      hcommonB hcommonC
  have hb : ∀ a : AL × AR,
      D.baseB (folkmanNativeTwoSortCode a) =
        folkmanNativeTwoSortCode (fBL a.1, fBR a.2) := by
    intro a
    simpa only [folkmanNativeTwoSortCode] using hbaseB a
  have hc : ∀ a : AL × AR,
      D.baseC (folkmanNativeTwoSortCode a) =
        folkmanNativeTwoSortCode (gCL a.1, gCR a.2) := by
    intro a
    simpa only [folkmanNativeTwoSortCode] using hbaseC a
  have hcomm : ∀ a : AL × AR,
      folkmanNativeEmbedB D (fBL a.1, fBR a.2) =
        folkmanNativeEmbedC D (gCL a.1, gCR a.2) := by
    intro a
    calc
      folkmanNativeEmbedB D (fBL a.1, fBR a.2) =
          D.embedB (D.baseB (folkmanNativeTwoSortCode a)) := by
            exact congrArg D.embedB (hb a).symm
      _ = D.embedC (D.baseC (folkmanNativeTwoSortCode a)) :=
          D.base_commutes _
      _ = folkmanNativeEmbedC D (gCL a.1, gCR a.2) := by
            exact congrArg D.embedC (hc a)
  refine ⟨{
    diagram := D
    pairing := βD
    additive_left := hleft
    additive_right := hright
    injective_B := folkmanNativeEmbedB_injective D
    injective_C := folkmanNativeEmbedC_injective D
    zero_B := folkmanNativeEmbedB_zero D
    zero_C := folkmanNativeEmbedC_zero D
    add_B := folkmanNativeEmbedB_add D
    add_C := folkmanNativeEmbedC_add D
    mul_B := folkmanNativeEmbedB_mul D
    mul_C := folkmanNativeEmbedC_mul D
    preserves_pairing_B := ?_
    preserves_pairing_C := ?_
    base_commutes := hcomm
    strong_intersection := ?_
  }⟩
  · intro x y
    simpa only [folkmanNativeEmbedB, folkmanNativeTwoSortCode] using hpB x y
  · intro x y
    simpa only [folkmanNativeEmbedC, folkmanNativeTwoSortCode] using hpC x y
  · intro b c
    exact folkmanNativeEmbed_images_eq_iff_common_base
      D fBL gCL fBR gCR hb hc b c

end SuccessorTree.NonPrecompact
