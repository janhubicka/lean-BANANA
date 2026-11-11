import BANANA.NonPrecompact.FolkmanNativeStrongAmalgamTarget
import BANANA.NonPrecompact.FolkmanNativePairingEmbedding

/-!
# Original-language embedding diagrams and sortwise strong intersection

This is an additional post-merge interface audit of finite Folkman
strong amalgamation. The amalgam has two independent Boolean-ring sorts.
For a multi-sorted strong amalgam, the exact intersection must be
valid separately in each sort, not only for pairs of elements.

The existing native strong-intersection theorem for pairs implies each
sortwise statement by taking zero in the other coordinate; non-unital
embeddings preserve zero. We also package each pair of component ring
maps as an actual original-language pairing embedding.

No preservation of a multiplicative unit or nonzero-sort assumption
is used. The zero-ring case is included. The countable limit and
dynamical assertions are outside this finite-class statement.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

-- The amalgam's finite atom types use the Boolean-algebra view of each
-- finite source ring; the corresponding instance is local to this file.
local instance folkmanNativeSortwiseAsBoolAlgFintype
    (α : Type*) [Fintype α] : Fintype (AsBoolAlg α) :=
  Fintype.ofEquiv α toBoolAlg

variable {AL BL CL AR BR CR : Type*}
variable [BooleanRing AL] [Fintype AL]
variable [BooleanRing BL] [Fintype BL]
variable [BooleanRing CL] [Fintype CL]
variable [BooleanRing AR] [Fintype AR]
variable [BooleanRing BR] [Fintype BR]
variable [BooleanRing CR] [Fintype CR]

variable {fBL : AL →ₙ+* BL} {gCL : AL →ₙ+* CL}
variable {fBR : AR →ₙ+* BR} {gCR : AR →ₙ+* CR}
variable {P : FolkmanNativeFinitePairing BL BR}
variable {Q : FolkmanNativeFinitePairing CL CR}

namespace FolkmanNativeStrongAmalgamCertificate

variable (S : FolkmanNativeStrongAmalgamCertificate
    fBL gCL fBR gCR P.pairing Q.pairing)

/-- The B-side maps are an embedding of the complete original
two-sorted language, not merely an embedding of the atom coordinates. -/
noncomputable def asNativeEmbeddingB :
    FolkmanNativePairingEmbedding P S.nativePairing where
  left := S.embedBLeft
  right := S.embedBRight
  left_injective := S.embedBLeft_injective
  right_injective := S.embedBRight_injective
  preserves_pairing := S.native_preserves_pairing_B

/-- The C-side maps are likewise a pairing-preserving embedding. -/
noncomputable def asNativeEmbeddingC :
    FolkmanNativePairingEmbedding Q S.nativePairing where
  left := S.embedCLeft
  right := S.embedCRight
  left_injective := S.embedCLeft_injective
  right_injective := S.embedCRight_injective
  preserves_pairing := S.native_preserves_pairing_C

/-- Exact strong intersection in the left sort alone. A right-sort
zero provides the missing coordinate in the previously verified
two-sorted intersection theorem. -/
theorem native_left_sort_intersection (b : BL) (c : CL) :
    S.embedBLeft b = S.embedCLeft c ↔
      ∃ a : AL, b = fBL a ∧ c = gCL a := by
  constructor
  · intro h
    have hzero :
        S.embedBRight (0 : BR) = S.embedCRight (0 : CR) := by
      simp
    obtain ⟨a, hb, hc⟩ :=
      (S.native_strong_intersection b (0 : BR) c (0 : CR)).mp
        ⟨h, hzero⟩
    exact ⟨a.1, congrArg Prod.fst hb, congrArg Prod.fst hc⟩
  · rintro ⟨a, rfl, rfl⟩
    exact S.native_base_commutes_left a

/-- Exact strong intersection in the right sort alone, using zero in
the left sort. -/
theorem native_right_sort_intersection (b : BR) (c : CR) :
    S.embedBRight b = S.embedCRight c ↔
      ∃ a : AR, b = fBR a ∧ c = gCR a := by
  constructor
  · intro h
    have hzero :
        S.embedBLeft (0 : BL) = S.embedCLeft (0 : CL) := by
      simp
    obtain ⟨a, hb, hc⟩ :=
      (S.native_strong_intersection (0 : BL) b (0 : CL) c).mp
        ⟨hzero, h⟩
    exact ⟨a.2, congrArg Prod.snd hb, congrArg Prod.snd hc⟩
  · rintro ⟨a, rfl, rfl⟩
    exact S.native_base_commutes_right a

/-- A direct two-sort strong-intersection certificate, as needed for
the finite multi-sorted Fraïssé class. -/
theorem native_sortwise_strong_intersection :
    (∀ (b : BL) (c : CL),
      S.embedBLeft b = S.embedCLeft c ↔
        ∃ a : AL, b = fBL a ∧ c = gCL a) ∧
    (∀ (b : BR) (c : CR),
      S.embedBRight b = S.embedCRight c ↔
        ∃ a : AR, b = fBR a ∧ c = gCR a) := by
  exact ⟨S.native_left_sort_intersection,
    S.native_right_sort_intersection⟩

end FolkmanNativeStrongAmalgamCertificate
end SuccessorTree.NonPrecompact
