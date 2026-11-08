import BANANA.NonPrecompact.FolkmanNativeStrongAmalgamPackage
import BANANA.NonPrecompact.FolkmanNativeFinitePairingClass

/-!
# Native Boolean-ring target of the finite Folkman strong amalgam

The existing atom-grid amalgam has two finite sets of amalgam atoms
with symmetric difference, intersection, and a biadditive pairing.
We equip those carriers with actual Boolean-ring structures and
represent all four original injections by non-unital homomorphisms.

This module is an unverified internal candidate pending Lean and axiom
audits; the circulation manuscript is unchanged.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff BigOperators

local instance folkmanNativeAmalgamAlgFintype (α : Type*) [Fintype α] :
    Fintype (AsBoolAlg α) := Fintype.ofEquiv α toBoolAlg

variable {AL BL CL AR BR CR : Type*}
variable [BooleanRing AL] [Fintype AL]
variable [BooleanRing BL] [Fintype BL]
variable [BooleanRing CL] [Fintype CL]
variable [BooleanRing AR] [Fintype AR]
variable [BooleanRing BR] [Fintype BR]
variable [BooleanRing CR] [Fintype CR]

variable {fBL : AL →ₙ+* BL} {gCL : AL →ₙ+* CL}
variable {fBR : AR →ₙ+* BR} {gCR : AR →ₙ+* CR}
variable {γB : BL → BR → F2} {γC : CL → CR → F2}

namespace FolkmanNativeStrongAmalgamCertificate

variable (S : FolkmanNativeStrongAmalgamCertificate
    fBL gCL fBR gCR γB γC)

/-- Actual finite Boolean ring on the left amalgam's atom sets. -/
abbrev NativeLeft : Type* :=
  AsBoolRing (Finset (FolkmanAtomAmalgam S.diagram.fL S.diagram.gL))

/-- Actual finite Boolean ring on the right amalgam's atom sets. -/
abbrev NativeRight : Type* :=
  AsBoolRing (Finset (FolkmanAtomAmalgam S.diagram.fR S.diagram.gR))

/-- Both target rings are finite, even when there are no atoms. -/
noncomputable instance nativeLeftFintype : Fintype S.NativeLeft := by
  classical
  exact Fintype.ofEquiv
    (Finset (FolkmanAtomAmalgam S.diagram.fL S.diagram.gL)) toBoolRing

noncomputable instance nativeRightFintype : Fintype S.NativeRight := by
  classical
  exact Fintype.ofEquiv
    (Finset (FolkmanAtomAmalgam S.diagram.fR S.diagram.gR)) toBoolRing

/-- The bilinear pairing as one on the two native Boolean rings. -/
noncomputable def nativePairing :
    FolkmanNativeFinitePairing S.NativeLeft S.NativeRight where
  pairing := fun x y => S.pairing (ofBoolRing x) (ofBoolRing y)
  add_left := by
    intro x x' y
    change S.pairing (symmDiff (ofBoolRing x) (ofBoolRing x'))
      (ofBoolRing y) = S.pairing (ofBoolRing x) (ofBoolRing y) +
      S.pairing (ofBoolRing x') (ofBoolRing y)
    exact S.additive_left _ _ _
  add_right := by
    intro x y y'
    change S.pairing (ofBoolRing x)
      (symmDiff (ofBoolRing y) (ofBoolRing y')) =
      S.pairing (ofBoolRing x) (ofBoolRing y) +
      S.pairing (ofBoolRing x) (ofBoolRing y')
    exact S.additive_right _ _ _

/-- The B-side left-sort injection, without a unit-preservation field. -/
noncomputable def embedBLeft : BL →ₙ+* S.NativeLeft where
  toFun := fun x => toBoolRing ((folkmanNativeEmbedB S.diagram (x, (0 : BR))).1)
  map_zero' := by
    have h := congrArg (fun z => toBoolRing z.1) S.zero_B
    simpa only [Prod.fst, toBoolRing_bot] using h
  map_add' := by
    intro x y
    have h := congrArg (fun z => toBoolRing z.1)
      (S.add_B (x, (0 : BR)) (y, (0 : BR)))
    simpa only [add_zero, folkmanTwoSortSymmDiff, Prod.fst,
      toBoolRing_symmDiff] using h
  map_mul' := by
    intro x y
    have h := congrArg (fun z => toBoolRing z.1)
      (S.mul_B (x, (0 : BR)) (y, (0 : BR)))
    simpa only [mul_zero, folkmanTwoSortInter, Prod.fst,
      toBoolRing_inf] using h

/-- B-side right-sort injection. -/
noncomputable def embedBRight : BR →ₙ+* S.NativeRight where
  toFun := fun x => toBoolRing ((folkmanNativeEmbedB S.diagram ((0 : BL), x)).2)
  map_zero' := by
    have h := congrArg (fun z => toBoolRing z.2) S.zero_B
    simpa only [Prod.snd, toBoolRing_bot] using h
  map_add' := by
    intro x y
    have h := congrArg (fun z => toBoolRing z.2)
      (S.add_B ((0 : BL), x) ((0 : BL), y))
    simpa only [zero_add, folkmanTwoSortSymmDiff, Prod.snd,
      toBoolRing_symmDiff] using h
  map_mul' := by
    intro x y
    have h := congrArg (fun z => toBoolRing z.2)
      (S.mul_B ((0 : BL), x) ((0 : BL), y))
    simpa only [zero_mul, folkmanTwoSortInter, Prod.snd,
      toBoolRing_inf] using h

/-- C-side left-sort injection. -/
noncomputable def embedCLeft : CL →ₙ+* S.NativeLeft where
  toFun := fun x => toBoolRing ((folkmanNativeEmbedC S.diagram (x, (0 : CR))).1)
  map_zero' := by
    have h := congrArg (fun z => toBoolRing z.1) S.zero_C
    simpa only [Prod.fst, toBoolRing_bot] using h
  map_add' := by
    intro x y
    have h := congrArg (fun z => toBoolRing z.1)
      (S.add_C (x, (0 : CR)) (y, (0 : CR)))
    simpa only [add_zero, folkmanTwoSortSymmDiff, Prod.fst,
      toBoolRing_symmDiff] using h
  map_mul' := by
    intro x y
    have h := congrArg (fun z => toBoolRing z.1)
      (S.mul_C (x, (0 : CR)) (y, (0 : CR)))
    simpa only [mul_zero, folkmanTwoSortInter, Prod.fst,
      toBoolRing_inf] using h

/-- C-side right-sort injection. -/
noncomputable def embedCRight : CR →ₙ+* S.NativeRight where
  toFun := fun x => toBoolRing ((folkmanNativeEmbedC S.diagram ((0 : CL), x)).2)
  map_zero' := by
    have h := congrArg (fun z => toBoolRing z.2) S.zero_C
    simpa only [Prod.snd, toBoolRing_bot] using h
  map_add' := by
    intro x y
    have h := congrArg (fun z => toBoolRing z.2)
      (S.add_C ((0 : CL), x) ((0 : CL), y))
    simpa only [zero_add, folkmanTwoSortSymmDiff, Prod.snd,
      toBoolRing_symmDiff] using h
  map_mul' := by
    intro x y
    have h := congrArg (fun z => toBoolRing z.2)
      (S.mul_C ((0 : CL), x) ((0 : CL), y))
    simpa only [zero_mul, folkmanTwoSortInter, Prod.snd,
      toBoolRing_inf] using h

/-- Each of the four original-sort maps is injective. -/
theorem embedBLeft_injective : Function.Injective S.embedBLeft := by
  intro x y h
  have hl : (folkmanNativeEmbedB S.diagram (x, (0 : BR))).1 =
      (folkmanNativeEmbedB S.diagram (y, (0 : BR))).1 :=
    toBoolRing_inj.mp h
  have hr : (folkmanNativeEmbedB S.diagram (x, (0 : BR))).2 =
      (folkmanNativeEmbedB S.diagram (y, (0 : BR))).2 := rfl
  exact congrArg Prod.fst (S.injective_B (Prod.ext hl hr))

theorem embedBRight_injective : Function.Injective S.embedBRight := by
  intro x y h
  have hl : (folkmanNativeEmbedB S.diagram ((0 : BL), x)).1 =
      (folkmanNativeEmbedB S.diagram ((0 : BL), y)).1 := rfl
  have hr : (folkmanNativeEmbedB S.diagram ((0 : BL), x)).2 =
      (folkmanNativeEmbedB S.diagram ((0 : BL), y)).2 :=
    toBoolRing_inj.mp h
  exact congrArg Prod.snd (S.injective_B (Prod.ext hl hr))

theorem embedCLeft_injective : Function.Injective S.embedCLeft := by
  intro x y h
  have hl : (folkmanNativeEmbedC S.diagram (x, (0 : CR))).1 =
      (folkmanNativeEmbedC S.diagram (y, (0 : CR))).1 :=
    toBoolRing_inj.mp h
  have hr : (folkmanNativeEmbedC S.diagram (x, (0 : CR))).2 =
      (folkmanNativeEmbedC S.diagram (y, (0 : CR))).2 := rfl
  exact congrArg Prod.fst (S.injective_C (Prod.ext hl hr))

theorem embedCRight_injective : Function.Injective S.embedCRight := by
  intro x y h
  have hl : (folkmanNativeEmbedC S.diagram ((0 : CL), x)).1 =
      (folkmanNativeEmbedC S.diagram ((0 : CL), y)).1 := rfl
  have hr : (folkmanNativeEmbedC S.diagram ((0 : CL), x)).2 =
      (folkmanNativeEmbedC S.diagram ((0 : CL), y)).2 :=
    toBoolRing_inj.mp h
  exact congrArg Prod.snd (S.injective_C (Prod.ext hl hr))

/-- The two copies of the original base commute in both sorts. -/
theorem native_base_commutes_left (a : AL) :
    S.embedBLeft (fBL a) = S.embedCLeft (gCL a) := by
  have h := congrArg (fun z => toBoolRing z.1)
    (S.base_commutes (a, (0 : AR)))
  simpa only [map_zero] using h

theorem native_base_commutes_right (a : AR) :
    S.embedBRight (fBR a) = S.embedCRight (gCR a) := by
  have h := congrArg (fun z => toBoolRing z.2)
    (S.base_commutes ((0 : AL), a))
  simpa only [map_zero] using h

/-- Original pairings are preserved on arbitrary carrier elements. -/
theorem native_preserves_pairing_B (x : BL) (y : BR) :
    S.nativePairing.pairing (S.embedBLeft x) (S.embedBRight y) = γB x y := by
  change S.pairing (folkmanNativeEmbedB S.diagram (x, y)).1
    (folkmanNativeEmbedB S.diagram (x, y)).2 = γB x y
  exact S.preserves_pairing_B x y

theorem native_preserves_pairing_C (x : CL) (y : CR) :
    S.nativePairing.pairing (S.embedCLeft x) (S.embedCRight y) = γC x y := by
  change S.pairing (folkmanNativeEmbedC S.diagram (x, y)).1
    (folkmanNativeEmbedC S.diagram (x, y)).2 = γC x y
  exact S.preserves_pairing_C x y

/-- Strong intersection on both native target carriers. -/
theorem native_strong_intersection (bL : BL) (bR : BR)
    (cL : CL) (cR : CR) :
    (S.embedBLeft bL = S.embedCLeft cL ∧
     S.embedBRight bR = S.embedCRight cR) ↔
      ∃ a : AL × AR,
        (bL, bR) = (fBL a.1, fBR a.2) ∧
        (cL, cR) = (gCL a.1, gCR a.2) := by
  constructor
  · rintro ⟨hl, hr⟩
    have hl' : (folkmanNativeEmbedB S.diagram (bL, bR)).1 =
        (folkmanNativeEmbedC S.diagram (cL, cR)).1 :=
      toBoolRing_inj.mp hl
    have hr' : (folkmanNativeEmbedB S.diagram (bL, bR)).2 =
        (folkmanNativeEmbedC S.diagram (cL, cR)).2 :=
      toBoolRing_inj.mp hr
    exact (S.strong_intersection (bL, bR) (cL, cR)).mp (Prod.ext hl' hr')
  · intro h
    have hp := (S.strong_intersection (bL, bR) (cL, cR)).mpr h
    exact ⟨congrArg (fun z => toBoolRing z.1) hp,
      congrArg (fun z => toBoolRing z.2) hp⟩

/-- Pairing and ring laws for a native amalgamation target. -/
structure NativeTargetLaws : Prop where
  injective_BL : Function.Injective S.embedBLeft
  injective_BR : Function.Injective S.embedBRight
  injective_CL : Function.Injective S.embedCLeft
  injective_CR : Function.Injective S.embedCRight
  commutes_L : ∀ a : AL, S.embedBLeft (fBL a) = S.embedCLeft (gCL a)
  commutes_R : ∀ a : AR, S.embedBRight (fBR a) = S.embedCRight (gCR a)
  pairing_B : ∀ x : BL, ∀ y : BR,
    S.nativePairing.pairing (S.embedBLeft x) (S.embedBRight y) = γB x y
  pairing_C : ∀ x : CL, ∀ y : CR,
    S.nativePairing.pairing (S.embedCLeft x) (S.embedCRight y) = γC x y
  exact_intersection : ∀ (bL : BL) (bR : BR) (cL : CL) (cR : CR),
    (S.embedBLeft bL = S.embedCLeft cL ∧
     S.embedBRight bR = S.embedCRight cR) ↔
      ∃ a : AL × AR,
        (bL, bR) = (fBL a.1, fBR a.2) ∧
        (cL, cR) = (gCL a.1, gCR a.2)

/-- Recover the laws from the atom-grid certificate. -/
theorem nativeTargetLaws : S.NativeTargetLaws where
  injective_BL := S.embedBLeft_injective
  injective_BR := S.embedBRight_injective
  injective_CL := S.embedCLeft_injective
  injective_CR := S.embedCRight_injective
  commutes_L := S.native_base_commutes_left
  commutes_R := S.native_base_commutes_right
  pairing_B := S.native_preserves_pairing_B
  pairing_C := S.native_preserves_pairing_C
  exact_intersection := S.native_strong_intersection

end FolkmanNativeStrongAmalgamCertificate

/-- The original-language native finite strong amalgamation target. -/
theorem folkmanNative_exists_full_native_target
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
    ∃ S : FolkmanNativeStrongAmalgamCertificate
        fBL gCL fBR gCR γB γC,
      S.NativeTargetLaws := by
  obtain ⟨S⟩ := folkmanNative_exists_language_strong_amalgam
    fBL gCL fBR gCR hfBL hgCL hfBR hgCR γA γB γC
    hAleft hBleft hCleft hAright hBright hCright
    hcommonB hcommonC
  exact ⟨S, S.nativeTargetLaws⟩

end SuccessorTree.NonPrecompact
