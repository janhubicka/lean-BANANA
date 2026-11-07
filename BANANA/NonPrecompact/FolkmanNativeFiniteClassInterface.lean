import BANANA.NonPrecompact.FolkmanNativeFiniteCodeEmbedding
import BANANA.NonPrecompact.FolkmanNativeFinitePairingClass
import BANANA.NonPrecompact.FolkmanNativeJEP
import BANANA.NonPrecompact.FolkmanFiniteClassData

/-!
# Track B: finite Folkman class in its original non-unital language

The object in the manuscript is a *pair of finite Boolean rings* and an
additive cross-pairing.  We package the previously established native
pairing, atom-coordinate, joint-embedding and strong-amalgamation results
without replacing native embeddings by mere linear maps.

This module is deliberately independent of the global tuple-orbit and
Fraisse-limit development (Track C).  It does not claim that a countable
homogeneous limit has been built.  Exact-head Lean and axiom audits are
required before any circulation validation marker can be advanced.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators symmDiff

namespace FolkmanNativeFinitePairing

variable {L R : Type*}
variable [BooleanRing L] [Fintype L]
variable [BooleanRing R] [Fintype R]

/-- The finite atom matrix of a *native* two-sort pairing. -/
noncomputable def finiteAtomCode (P : FolkmanNativeFinitePairing L R) :
    FolkmanAtomStructure :=
  folkmanNativeFinCode P.pairing

/-- The code recovers the pairing on every original ring element,
not merely on pairs of atoms. -/
theorem finiteAtomCode_pairing (P : FolkmanNativeFinitePairing L R)
    (x : L) (y : R) :
    P.pairing x y =
      ∑ i ∈ folkmanNativeFinSupport L x,
        ∑ j ∈ folkmanNativeFinSupport R y,
          P.finiteAtomCode.edge i j := by
  exact folkmanNativeFinCode_pairing P.pairing P.add_left P.add_right x y

/-- A native object is isomorphic, in all operations of the original
non-unital language, to a finite atom presentation.  No nonzero-sort
or preservation-of-top hypotheses are imposed. -/
theorem exists_exact_finite_code (P : FolkmanNativeFinitePairing L R) :
    ∃ A : FolkmanAtomStructure,
      ∃ eL : L ≃ Finset (Fin A.leftCount),
        ∃ eR : R ≃ Finset (Fin A.rightCount),
          (∀ x : L, ∀ y : R,
            P.pairing x y = ∑ i ∈ eL x, ∑ j ∈ eR y, A.edge i j) ∧
          (∀ x x' : L, eL (x + x') = symmDiff (eL x) (eL x')) ∧
          (∀ y y' : R, eR (y + y') = symmDiff (eR y) (eR y')) ∧
          (∀ x x' : L, eL (x * x') = eL x ∩ eL x') ∧
          (∀ y y' : R, eR (y * y') = eR y ∩ eR y') ∧
          eL (0 : L) = ∅ ∧ eR (0 : R) = ∅ := by
  exact folkmanNative_exists_finite_index_presentation
    P.pairing P.add_left P.add_right

end FolkmanNativeFinitePairing

/-- The finite atom codes form a countable collection.  Combined with
`exists_exact_finite_code` this gives countably many finite native
isomorphism types. -/
theorem folkmanNativeFinite_codes_countable :
    Countable FolkmanAtomStructure := by
  infer_instance

/-- The finite native class has no upper bound on the number of atoms
in either sort. -/
theorem folkmanNativeFinite_codes_unbounded (n : ℕ) :
    ∃ A : FolkmanAtomStructure,
      n < A.leftCount ∧ n < A.rightCount :=
  folkmanAtomStructure_unbounded_both_sorts n

/-- Original-language joint embedding, for two *packaged* finite
bilinear pairings, using the two zero rings as the common base. -/
theorem folkmanNativeFinitePairing_joint_embedding
    {BL BR CL CR : Type*}
    [BooleanRing BL] [Fintype BL]
    [BooleanRing BR] [Fintype BR]
    [BooleanRing CL] [Fintype CL]
    [BooleanRing CR] [Fintype CR]
    (B : FolkmanNativeFinitePairing BL BR)
    (C : FolkmanNativeFinitePairing CL CR) :
    Nonempty (FolkmanNativeStrongAmalgamCertificate
      (0 : PUnit →ₙ+* BL) (0 : PUnit →ₙ+* CL)
      (0 : PUnit →ₙ+* BR) (0 : PUnit →ₙ+* CR)
      B.pairing C.pairing) := by
  exact folkmanNative_joint_embedding
    B.pairing C.pairing
    B.add_left C.add_left B.add_right C.add_right

/-- Strong amalgamation with exact intersections on the *original*
finite Boolean-ring carriers.  All maps are injective non-unital ring
homomorphisms, and both original cross-pairings are preserved. -/
theorem folkmanNativeFinitePairing_strong_amalgamation
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
    (A : FolkmanNativeFinitePairing AL AR)
    (B : FolkmanNativeFinitePairing BL BR)
    (C : FolkmanNativeFinitePairing CL CR)
    (hcommonB : ∀ a r, B.pairing (fBL a) (fBR r) = A.pairing a r)
    (hcommonC : ∀ a r, C.pairing (gCL a) (gCR r) = A.pairing a r) :
    Nonempty (FolkmanNativeStrongAmalgamCertificate
      fBL gCL fBR gCR B.pairing C.pairing) := by
  exact folkmanNative_exists_language_strong_amalgam
    fBL gCL fBR gCR hfBL hgCL hfBR hgCR
    A.pairing B.pairing C.pairing
    A.add_left B.add_left C.add_left
    A.add_right B.add_right C.add_right
    hcommonB hcommonC

end SuccessorTree.NonPrecompact
