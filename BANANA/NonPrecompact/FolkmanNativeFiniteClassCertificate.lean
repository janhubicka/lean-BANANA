import BANANA.NonPrecompact.FolkmanNativeFiniteHeredity
import BANANA.NonPrecompact.FolkmanNativeFiniteCodeRealisation

/-!
# Class-level finite Folkman--BANANA certificate

This module assembles the exact finite-class ingredients used in the
circulation proposition: hereditary closure in the original non-unital
language, joint embedding, strong amalgamation, a countable family of
native representatives, and arbitrarily large native objects.

This is deliberately a certificate of the mathematical ingredients rather
than an ad-hoc redefinition of a general Fraïssé-class library.  It does not
construct the countable homogeneous limit or assert any automorphism-orbit
statement.
-/

namespace SuccessorTree.NonPrecompact

/-- The finite original-language properties needed to conclude that the
Folkman--BANANA age is a strong-amalgamation Fraïssé class.  The quantified
carriers are ordinary small finite types; arbitrary finite native objects
are represented by the countable atom-code family below. -/
structure FolkmanNativeFiniteClassCertificate where
  hereditary :
    ∀ {L R : Type} [BooleanRing L] [BooleanRing R]
      (P : FolkmanNativeFinitePairing L R)
      (SL : NonUnitalSubring L) (SR : NonUnitalSubring R)
      [Fintype SL] [Fintype SR],
      letI := folkmanNativeSubringBooleanRing SL
      letI := folkmanNativeSubringBooleanRing SR
      ∃ (Q : FolkmanNativeFinitePairing SL SR)
        (iL : SL →ₙ+* L) (iR : SR →ₙ+* R),
        Function.Injective iL ∧ Function.Injective iR ∧
        (∀ x : SL, iL x = (x : L)) ∧
        (∀ y : SR, iR y = (y : R)) ∧
        (∀ x y, Q.pairing x y = P.pairing (iL x) (iR y))
  joint_embedding :
    ∀ {BL BR CL CR : Type}
      [BooleanRing BL] [Fintype BL]
      [BooleanRing BR] [Fintype BR]
      [BooleanRing CL] [Fintype CL]
      [BooleanRing CR] [Fintype CR]
      (B : FolkmanNativeFinitePairing BL BR)
      (C : FolkmanNativeFinitePairing CL CR),
      Nonempty (FolkmanNativeStrongAmalgamCertificate
        (0 : PUnit.{1} →ₙ+* BL) (0 : PUnit.{1} →ₙ+* CL)
        (0 : PUnit.{1} →ₙ+* BR) (0 : PUnit.{1} →ₙ+* CR)
        B.pairing C.pairing)
  strong_amalgamation :
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
      Nonempty (FolkmanNativeStrongAmalgamCertificate
        fBL gCL fBR gCR B.pairing C.pairing)
  code_family_countable : Countable FolkmanAtomStructure
  native_representative :
    ∀ {L R : Type}
      [BooleanRing L] [Fintype L]
      [BooleanRing R] [Fintype R]
      (P : FolkmanNativeFinitePairing L R),
      ∃ A : FolkmanAtomStructure,
        Nonempty (FolkmanNativeFinitePairingIso P
          (folkmanNativeCodeRealisation A))
  arbitrarily_large :
    ∀ n : ℕ,
      ∃ P : FolkmanNativeFinitePairing
          (FolkmanNativeCodeRing (n + 1)) (FolkmanNativeCodeRing (n + 1)),
        n < Fintype.card (FolkmanNativeCodeRing (n + 1)) ∧
          n < Fintype.card (FolkmanNativeCodeRing (n + 1))

/-- All five finite-class ingredients are supplied by the independently
developed native-language modules. -/
noncomputable def folkmanNativeFiniteClassCertificate :
    FolkmanNativeFiniteClassCertificate where
  hereditary := by
    intro L R _ _ P SL SR _ _
    exact folkmanNativeFinite_hereditary P SL SR
  joint_embedding := by
    intro BL BR CL CR _ _ _ _ _ _ _ _ B C
    exact folkmanNativeFinitePairing_joint_embedding B C
  strong_amalgamation := by
    intro AL BL CL AR BR CR
      _ _ _ _ _ _ _ _ _ _ _ _
      fBL gCL fBR gCR hfBL hgCL hfBR hgCR A B C hcommonB hcommonC
    exact folkmanNativeFinitePairing_strong_amalgamation
      fBL gCL fBR gCR hfBL hgCL hfBR hgCR A B C hcommonB hcommonC
  code_family_countable := by infer_instance
  native_representative := by
    intro L R _ _ _ _ P
    exact (folkmanNativeFinite_countable_native_representatives P).2
  arbitrarily_large := folkmanNativeFinite_native_objects_unbounded

/-- The countability statement is genuinely about native isomorphism
representatives: every finite native object is isomorphic to an object in
one fixed countable code-indexed family. -/
theorem folkmanNativeFiniteClass_countable_representatives
    {L R : Type}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (P : FolkmanNativeFinitePairing L R) :
    ∃ A : FolkmanAtomStructure,
      Nonempty (FolkmanNativeFinitePairingIso P
        (folkmanNativeCodeRealisation A)) :=
  folkmanNativeFiniteClassCertificate.native_representative P

end SuccessorTree.NonPrecompact
