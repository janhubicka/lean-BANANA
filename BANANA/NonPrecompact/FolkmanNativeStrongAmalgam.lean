import BANANA.NonPrecompact.FolkmanNativePairingCompatibility
import BANANA.NonPrecompact.FolkmanNativeTwoSortOwnerDiagram
import BANANA.NonPrecompact.FolkmanFiniteStrongAmalgamPairing

/-!
# Finite native two-sorted Folkman strong-amalgamation certificate

This combines the four native non-unital ring embeddings, their atom
owner diagram, the transport of three bilinear pairings and the
finite-atom strong-amalgamation certificate. The resulting actual
atom-grid rings preserve both native pairings and have exact common
intersection in the two sorts.

The ambient rings are represented by finite subsets of their atoms.
A separate Fraïssé-class interface remains to package heredity,
joint embedding and the finite language.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff

local instance folkmanAsBoolAlgFiniteForStrongAmalgam
    (γ : Type*) [Fintype γ] : Fintype (AsBoolAlg γ) :=
  Fintype.ofEquiv γ toBoolAlg

/-- Native non-unital Boolean-ring diagrams with compatible bilinear
pairings have a common finite-atom ring-pair amalgam: both native
source pairings are preserved and the two images meet exactly in the
base. In particular, this includes zero rings on either sort. -/
theorem folkmanNativeTwoSort_exists_strongAmalgamPairing
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
        (∀ x x' y, βD (symmDiff x x') y =
          βD x y + βD x' y) ∧
        (∀ x y y', βD x (symmDiff y y') =
          βD x y + βD x y') ∧
        (∀ x : BL, ∀ y : BR,
          βD (D.embedB (folkmanNativeRingAtomEquiv BL x,
            folkmanNativeRingAtomEquiv BR y)).1
            (D.embedB (folkmanNativeRingAtomEquiv BL x,
              folkmanNativeRingAtomEquiv BR y)).2 = γB x y) ∧
        (∀ x : CL, ∀ y : CR,
          βD (D.embedC (folkmanNativeRingAtomEquiv CL x,
            folkmanNativeRingAtomEquiv CR y)).1
            (D.embedC (folkmanNativeRingAtomEquiv CL x,
              folkmanNativeRingAtomEquiv CR y)).2 = γC x y) ∧
        (∀ b : Finset (PrebananaAbstractAtoms (AsBoolAlg BL)) ×
                 Finset (PrebananaAbstractAtoms (AsBoolAlg BR)),
          ∀ c : Finset (PrebananaAbstractAtoms (AsBoolAlg CL)) ×
                 Finset (PrebananaAbstractAtoms (AsBoolAlg CR)),
            D.embedB b = D.embedC c ↔
              ∃ a : Finset (PrebananaAbstractAtoms (AsBoolAlg AL)) ×
                      Finset (PrebananaAbstractAtoms (AsBoolAlg AR)),
                b = D.baseB a ∧ c = D.baseC a) ∧
        (∀ a : AL × AR,
          D.baseB (folkmanNativeRingAtomEquiv AL a.1,
            folkmanNativeRingAtomEquiv AR a.2) =
            (folkmanNativeRingAtomEquiv BL (fBL a.1),
              folkmanNativeRingAtomEquiv BR (fBR a.2))) ∧
        (∀ a : AL × AR,
          D.baseC (folkmanNativeRingAtomEquiv AL a.1,
            folkmanNativeRingAtomEquiv AR a.2) =
            (folkmanNativeRingAtomEquiv CL (gCL a.1),
              folkmanNativeRingAtomEquiv CR (gCR a.2))) := by
  classical
  obtain ⟨D, hBL, hCL, hBR, hCR⟩ :=
    folkmanNativeTwoSort_exists_atomDiagram
      fBL gCL fBR gCR hfBL hgCL hfBR hgCR
  have hBL' (s : Finset (PrebananaAbstractAtoms (AsBoolAlg AL))) :
      prebananaAbstractPowersetMap
        (fun x : AsBoolAlg AL => toBoolAlg (fBL (ofBoolAlg x))) s =
        folkmanFinsetBaseLeft D.fL s := by
    ext b
    have hb := (Finset.ext_iff.mp (hBL s)) b
    simpa only [folkmanFinsetBaseLeft, Finset.mem_filter, Finset.mem_univ, true_and] using hb
  have hBR' (s : Finset (PrebananaAbstractAtoms (AsBoolAlg AR))) :
      prebananaAbstractPowersetMap
        (fun x : AsBoolAlg AR => toBoolAlg (fBR (ofBoolAlg x))) s =
        folkmanFinsetBaseLeft D.fR s := by
    ext b
    have hb := (Finset.ext_iff.mp (hBR s)) b
    simpa only [folkmanFinsetBaseLeft, Finset.mem_filter, Finset.mem_univ, true_and] using hb
  have hCL' (s : Finset (PrebananaAbstractAtoms (AsBoolAlg AL))) :
      prebananaAbstractPowersetMap
        (fun x : AsBoolAlg AL => toBoolAlg (gCL (ofBoolAlg x))) s =
        folkmanFinsetBaseRight D.gL s := by
    ext b
    have hb := (Finset.ext_iff.mp (hCL s)) b
    simpa only [folkmanFinsetBaseRight, Finset.mem_filter, Finset.mem_univ, true_and] using hb
  have hCR' (s : Finset (PrebananaAbstractAtoms (AsBoolAlg AR))) :
      prebananaAbstractPowersetMap
        (fun x : AsBoolAlg AR => toBoolAlg (gCR (ofBoolAlg x))) s =
        folkmanFinsetBaseRight D.gR s := by
    ext b
    have hb := (Finset.ext_iff.mp (hCR s)) b
    simpa only [folkmanFinsetBaseRight, Finset.mem_filter, Finset.mem_univ, true_and] using hb
  have hBco (a : Finset (PrebananaAbstractAtoms (AsBoolAlg AL)))
      (r : Finset (PrebananaAbstractAtoms (AsBoolAlg AR))) :
      folkmanNativeTransportPairing γB
        (folkmanFinsetBaseLeft D.fL a)
        (folkmanFinsetBaseLeft D.fR r) =
      folkmanNativeTransportPairing γA a r := by
    rw [← hBL' a, ← hBR' r]
    exact folkmanNativeTransportPairing_compatible
      fBL fBR γA γB hcommonB a r
  have hCco (a : Finset (PrebananaAbstractAtoms (AsBoolAlg AL)))
      (r : Finset (PrebananaAbstractAtoms (AsBoolAlg AR))) :
      folkmanNativeTransportPairing γC
        (folkmanFinsetBaseRight D.gL a)
        (folkmanFinsetBaseRight D.gR r) =
      folkmanNativeTransportPairing γA a r := by
    rw [← hCL' a, ← hCR' r]
    exact folkmanNativeTransportPairing_compatible
      gCL gCR γA γC hcommonC a r
  obtain ⟨βD, hDleft, hDright, hDB, hDC, hIntersection⟩ :=
    D.exists_strong_amalgam_pairing
      (folkmanNativeTransportPairing γA)
      (folkmanNativeTransportPairing γB)
      (folkmanNativeTransportPairing γC)
      (fun x x' y => by
        convert folkmanNativeTransportPairing_add_left γA hAleft x x' y using 1
          <;> first | rfl |
            (congr 1; ext z; simp only [Finset.mem_symmDiff]))
      (fun x x' y => by
        convert folkmanNativeTransportPairing_add_left γB hBleft x x' y using 1
          <;> first | rfl |
            (congr 1; ext z; simp only [Finset.mem_symmDiff]))
      (fun x x' y => by
        convert folkmanNativeTransportPairing_add_left γC hCleft x x' y using 1
          <;> first | rfl |
            (congr 1; ext z; simp only [Finset.mem_symmDiff]))
      (fun x y y' => by
        convert folkmanNativeTransportPairing_add_right γA hAright x y y' using 1
          <;> first | rfl |
            (congr 1; ext z; simp only [Finset.mem_symmDiff]))
      (fun x y y' => by
        convert folkmanNativeTransportPairing_add_right γB hBright x y y' using 1
          <;> first | rfl |
            (congr 1; ext z; simp only [Finset.mem_symmDiff]))
      (fun x y y' => by
        convert folkmanNativeTransportPairing_add_right γC hCright x y y' using 1
          <;> first | rfl |
            (congr 1; ext z; simp only [Finset.mem_symmDiff]))
      hBco hCco
  refine ⟨D, βD, ?_, ?_, ?_, ?_,
    hIntersection, ?_, ?_⟩
  · intro x x' y
    convert hDleft x x' y using 1
      <;> first | rfl |
        (congr 1; ext z; simp only [Finset.mem_symmDiff])
  · intro x y y'
    convert hDright x y y' using 1
      <;> first | rfl |
        (congr 1; ext z; simp only [Finset.mem_symmDiff])
  · intro x y
    simpa only [folkmanNativeTransportPairing_apply_codes] using
      hDB (folkmanNativeRingAtomEquiv BL x)
        (folkmanNativeRingAtomEquiv BR y)
  · intro x y
    simpa only [folkmanNativeTransportPairing_apply_codes] using
      hDC (folkmanNativeRingAtomEquiv CL x)
        (folkmanNativeRingAtomEquiv CR y)
  · intro a
    apply Prod.ext
    · change folkmanFinsetBaseLeft D.fL
          (folkmanNativeRingAtomEquiv AL a.1) =
        folkmanNativeRingAtomEquiv BL (fBL a.1)
      rw [← hBL' (folkmanNativeRingAtomEquiv AL a.1),
          ← folkmanNativeRingAtomEquiv_map fBL
            (folkmanNativeRingAtomEquiv AL a.1)]
      simp
    · change folkmanFinsetBaseLeft D.fR
          (folkmanNativeRingAtomEquiv AR a.2) =
        folkmanNativeRingAtomEquiv BR (fBR a.2)
      rw [← hBR' (folkmanNativeRingAtomEquiv AR a.2),
          ← folkmanNativeRingAtomEquiv_map fBR
            (folkmanNativeRingAtomEquiv AR a.2)]
      simp
  · intro a
    apply Prod.ext
    · change folkmanFinsetBaseRight D.gL
          (folkmanNativeRingAtomEquiv AL a.1) =
        folkmanNativeRingAtomEquiv CL (gCL a.1)
      rw [← hCL' (folkmanNativeRingAtomEquiv AL a.1),
          ← folkmanNativeRingAtomEquiv_map gCL
            (folkmanNativeRingAtomEquiv AL a.1)]
      simp
    · change folkmanFinsetBaseRight D.gR
          (folkmanNativeRingAtomEquiv AR a.2) =
        folkmanNativeRingAtomEquiv CR (gCR a.2)
      rw [← hCR' (folkmanNativeRingAtomEquiv AR a.2),
          ← folkmanNativeRingAtomEquiv_map gCR
            (folkmanNativeRingAtomEquiv AR a.2)]
      simp

end SuccessorTree.NonPrecompact
