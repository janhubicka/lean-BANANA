import BANANA.NonPrecompact.FolkmanNativeRingAtomEquiv
import BANANA.NonPrecompact.FolkmanFiniteTwoSortRingDiagram

/-!
# Native source embeddings in the Folkman two-sort atom amalgam

Each native finite Boolean-ring pair is coded by finite subsets of
atoms. Composing that canonical code with the verified actual-grid
embeddings produces maps on the original pair of native ring carriers.

This module records injectivity and preservation of zero, additive
symmetric difference, and multiplicative intersection in both sorts.
Together with pairing preservation and exact intersection, these are
the operations required in a finite Folkman strong amalgamation.
Non-unital embeddings and the zero ring are permitted.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff

local instance folkmanAsBoolAlgFiniteForNativeEmbeddings
    (γ : Type*) [Fintype γ] : Fintype (AsBoolAlg γ) :=
  Fintype.ofEquiv γ toBoolAlg

/-- Encode a two-sort native Boolean-ring carrier by its two
canonical finite sets of atoms. -/
noncomputable def folkmanNativeTwoSortCode
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (x : L × R) :
    Finset (PrebananaAbstractAtoms (AsBoolAlg L)) ×
      Finset (PrebananaAbstractAtoms (AsBoolAlg R)) :=
  (folkmanNativeRingAtomEquiv L x.1,
   folkmanNativeRingAtomEquiv R x.2)

/-- Native ring-pair atom coordinates preserve the pair of zeros. -/
theorem folkmanNativeTwoSortCode_zero
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R] :
    folkmanNativeTwoSortCode ((0 : L), (0 : R)) = (∅, ∅) := by
  change
    (folkmanNativeRingAtomEquiv L (0 : L),
      folkmanNativeRingAtomEquiv R (0 : R)) = (∅, ∅)
  rw [folkmanNativeRingAtomEquiv_zero, folkmanNativeRingAtomEquiv_zero]

/-- Coordinates turn componentwise native addition into symmetric
difference in each sort. -/
theorem folkmanNativeTwoSortCode_add
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (x y : L × R) :
    folkmanNativeTwoSortCode (x.1 + y.1, x.2 + y.2) =
      folkmanTwoSortSymmDiff
        (folkmanNativeTwoSortCode x)
        (folkmanNativeTwoSortCode y) := by
  classical
  apply Prod.ext
  · ext a
    simp only [folkmanNativeTwoSortCode, folkmanTwoSortSymmDiff,
      Prod.fst, folkmanNativeRingAtomEquiv_add, Finset.mem_symmDiff]
  · ext a
    simp only [folkmanNativeTwoSortCode, folkmanTwoSortSymmDiff,
      Prod.snd, folkmanNativeRingAtomEquiv_add, Finset.mem_symmDiff]

/-- Coordinates turn componentwise native multiplication into
intersection in each sort. -/
theorem folkmanNativeTwoSortCode_mul
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (x y : L × R) :
    folkmanNativeTwoSortCode (x.1 * y.1, x.2 * y.2) =
      folkmanTwoSortInter
        (folkmanNativeTwoSortCode x)
        (folkmanNativeTwoSortCode y) := by
  classical
  apply Prod.ext
  · ext a
    simp only [folkmanNativeTwoSortCode, folkmanTwoSortInter,
      Prod.fst, folkmanNativeRingAtomEquiv_mul, Finset.mem_inter]
  · ext a
    simp only [folkmanNativeTwoSortCode, folkmanTwoSortInter,
      Prod.snd, folkmanNativeRingAtomEquiv_mul, Finset.mem_inter]

/-- The two-sort canonical native code is faithful. -/
theorem folkmanNativeTwoSortCode_injective
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R] :
    Function.Injective
      (folkmanNativeTwoSortCode (L := L) (R := R)) := by
  intro x y h
  have hL : folkmanNativeRingAtomEquiv L x.1 =
      folkmanNativeRingAtomEquiv L y.1 := congrArg Prod.fst h
  have hR : folkmanNativeRingAtomEquiv R x.2 =
      folkmanNativeRingAtomEquiv R y.2 := congrArg Prod.snd h
  exact Prod.ext
    ((folkmanNativeRingAtomEquiv L).injective hL)
    ((folkmanNativeRingAtomEquiv R).injective hR)

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

/-- Embed original B-side native elements in the actual atom-grid rings. -/
noncomputable def folkmanNativeEmbedB (x : BL × BR) :
    Finset (FolkmanAtomAmalgam D.fL D.gL) ×
      Finset (FolkmanAtomAmalgam D.fR D.gR) :=
  D.embedB (folkmanNativeTwoSortCode x)

/-- Embed original C-side native elements in the actual atom-grid rings. -/
noncomputable def folkmanNativeEmbedC (x : CL × CR) :
    Finset (FolkmanAtomAmalgam D.fL D.gL) ×
      Finset (FolkmanAtomAmalgam D.fR D.gR) :=
  D.embedC (folkmanNativeTwoSortCode x)

theorem folkmanNativeEmbedB_injective :
    Function.Injective (folkmanNativeEmbedB D) := by
  intro x y h
  exact folkmanNativeTwoSortCode_injective
    (D.embedB_injective h)

theorem folkmanNativeEmbedC_injective :
    Function.Injective (folkmanNativeEmbedC D) := by
  intro x y h
  exact folkmanNativeTwoSortCode_injective
    (D.embedC_injective h)

theorem folkmanNativeEmbedB_zero :
    folkmanNativeEmbedB D ((0 : BL), (0 : BR)) = (∅, ∅) := by
  change D.embedB (folkmanNativeTwoSortCode ((0 : BL), (0 : BR))) = (∅, ∅)
  rw [folkmanNativeTwoSortCode_zero]
  exact D.embedB_zero

theorem folkmanNativeEmbedC_zero :
    folkmanNativeEmbedC D ((0 : CL), (0 : CR)) = (∅, ∅) := by
  change D.embedC (folkmanNativeTwoSortCode ((0 : CL), (0 : CR))) = (∅, ∅)
  rw [folkmanNativeTwoSortCode_zero]
  exact D.embedC_zero

theorem folkmanNativeEmbedB_add (x y : BL × BR) :
    folkmanNativeEmbedB D (x.1 + y.1, x.2 + y.2) =
      folkmanTwoSortSymmDiff (folkmanNativeEmbedB D x)
        (folkmanNativeEmbedB D y) := by
  change D.embedB (folkmanNativeTwoSortCode (x.1 + y.1, x.2 + y.2)) =
    folkmanTwoSortSymmDiff
      (D.embedB (folkmanNativeTwoSortCode x))
      (D.embedB (folkmanNativeTwoSortCode y))
  rw [folkmanNativeTwoSortCode_add]
  exact D.embedB_symmDiff _ _

theorem folkmanNativeEmbedC_add (x y : CL × CR) :
    folkmanNativeEmbedC D (x.1 + y.1, x.2 + y.2) =
      folkmanTwoSortSymmDiff (folkmanNativeEmbedC D x)
        (folkmanNativeEmbedC D y) := by
  change D.embedC (folkmanNativeTwoSortCode (x.1 + y.1, x.2 + y.2)) =
    folkmanTwoSortSymmDiff
      (D.embedC (folkmanNativeTwoSortCode x))
      (D.embedC (folkmanNativeTwoSortCode y))
  rw [folkmanNativeTwoSortCode_add]
  exact D.embedC_symmDiff _ _

theorem folkmanNativeEmbedB_mul (x y : BL × BR) :
    folkmanNativeEmbedB D (x.1 * y.1, x.2 * y.2) =
      folkmanTwoSortInter (folkmanNativeEmbedB D x)
        (folkmanNativeEmbedB D y) := by
  change D.embedB (folkmanNativeTwoSortCode (x.1 * y.1, x.2 * y.2)) =
    folkmanTwoSortInter
      (D.embedB (folkmanNativeTwoSortCode x))
      (D.embedB (folkmanNativeTwoSortCode y))
  rw [folkmanNativeTwoSortCode_mul]
  exact D.embedB_inter _ _

theorem folkmanNativeEmbedC_mul (x y : CL × CR) :
    folkmanNativeEmbedC D (x.1 * y.1, x.2 * y.2) =
      folkmanTwoSortInter (folkmanNativeEmbedC D x)
        (folkmanNativeEmbedC D y) := by
  change D.embedC (folkmanNativeTwoSortCode (x.1 * y.1, x.2 * y.2)) =
    folkmanTwoSortInter
      (D.embedC (folkmanNativeTwoSortCode x))
      (D.embedC (folkmanNativeTwoSortCode y))
  rw [folkmanNativeTwoSortCode_mul]
  exact D.embedC_inter _ _

end SuccessorTree.NonPrecompact
