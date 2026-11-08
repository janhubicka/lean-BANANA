import BANANA.NonPrecompact.FolkmanNativeFiniteClassCertificate
import BANANA.NonPrecompact.FolkmanNativeStrongAmalgamTarget

/-!
# Original-language finite Folkman class certificate

The finite class has hereditary closure, joint embedding, strong
amalgamation, countably many native isomorphism representatives and
arbitrarily large finite members. This file combines those checked
facts with *actual finite Boolean-ring target structures* for JEP
and strong AP, rather than leaving the targets as atom diagrams.

Embeddings preserve the two ring operations, zero and the cross-pairing,
but not necessarily the multiplicative unit. The zero ring is allowed
on either sort; unowned target atoms are retained. This does NOT
construct the Fraïssé limit or establish ω-categoricity or amenability.

Internal Lean source only. The circulation manuscript remains frozen.
-/

namespace SuccessorTree.NonPrecompact

/-- A complete certificate for the finite class in its original
two-sorted non-unital language. The first component records heredity,
countable representatives and unboundedness as well as the finite
amalgamation data; the remaining fields assert that JEP and strong
AP have actual native Boolean-ring targets. -/
structure FolkmanNativeCompleteFiniteClassCertificate where
  finite : FolkmanNativeFiniteClassCertificate
  native_joint_embedding :
    ∀ {BL BR CL CR : Type}
      [BooleanRing BL] [Fintype BL]
      [BooleanRing BR] [Fintype BR]
      [BooleanRing CL] [Fintype CL]
      [BooleanRing CR] [Fintype CR]
      (B : FolkmanNativeFinitePairing BL BR)
      (C : FolkmanNativeFinitePairing CL CR),
      ∃ S : FolkmanNativeStrongAmalgamCertificate
        (0 : PUnit.{1} →ₙ+* BL) (0 : PUnit.{1} →ₙ+* CL)
        (0 : PUnit.{1} →ₙ+* BR) (0 : PUnit.{1} →ₙ+* CR)
        B.pairing C.pairing,
        S.NativeTargetLaws
  native_strong_amalgamation :
    ∀ {AL BL CL AR BR CR : Type}
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
      (A : FolkmanNativeFinitePairing AL AR)
      (B : FolkmanNativeFinitePairing BL BR)
      (C : FolkmanNativeFinitePairing CL CR)
      (hcommonB : ∀ a r, B.pairing (fBL a) (fBR r) = A.pairing a r)
      (hcommonC : ∀ a r, C.pairing (gCL a) (gCR r) = A.pairing a r),
      ∃ S : FolkmanNativeStrongAmalgamCertificate
        fBL gCL fBR gCR B.pairing C.pairing,
        S.NativeTargetLaws

/-- All finite original-language class ingredients have a common
certificate, including actual native target witnesses for JEP and AP. -/
noncomputable def folkmanNativeCompleteFiniteClassCertificate :
    FolkmanNativeCompleteFiniteClassCertificate where
  finite := folkmanNativeFiniteClassCertificate
  native_joint_embedding := by
    intro BL BR CL CR _ _ _ _ _ _ _ _ B C
    obtain ⟨S⟩ := folkmanNativeFiniteClassCertificate.joint_embedding B C
    exact ⟨S, S.nativeTargetLaws⟩
  native_strong_amalgamation := by
    intro AL BL CL AR BR CR
      _ _ _ _ _ _ _ _ _ _ _ _
      fBL gCL fBR gCR hfBL hgCL hfBR hgCR A B C hcommonB hcommonC
    obtain ⟨S⟩ := folkmanNativeFiniteClassCertificate.strong_amalgamation
      fBL gCL fBR gCR hfBL hgCL hfBR hgCR A B C hcommonB hcommonC
    exact ⟨S, S.nativeTargetLaws⟩

/-- The finite-class result is inhabited by the assembled original-
language certificate, including the zero-ring and non-unital cases. -/
theorem folkmanNativeCompleteFiniteClass_nonempty :
    Nonempty FolkmanNativeCompleteFiniteClassCertificate :=
  ⟨folkmanNativeCompleteFiniteClassCertificate⟩

end SuccessorTree.NonPrecompact
