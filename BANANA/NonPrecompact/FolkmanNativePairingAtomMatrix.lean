import BANANA.NonPrecompact.FolkmanAtomMatrixReconstruction
import BANANA.NonPrecompact.FolkmanNativePairingTransport

/-!
# Native finite Folkman pairings are determined by their atom matrices

The canonical atom equivalence of every finite Boolean ring converts
addition to symmetric difference.  Pairing transport preserves both
additivity laws.  The generic finite-set reconstruction lemma therefore
gives a matrix on the two finite atom types which recovers the pairing
of every original pair of native ring elements.

In particular this includes zero rings and requires neither unital
embeddings nor any choice of additive bases apart from ring atoms.
The final step of enumerating atom types by Fin and packaging
isomorphism representatives is separate.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff BigOperators

local instance folkmanAsBoolAlgFiniteForAtomMatrix
    (α : Type*) [Fintype α] : Fintype (AsBoolAlg α) :=
  Fintype.ofEquiv α toBoolAlg

/-- The native F₂-pairing matrix indexed by atoms of both sorts. -/
noncomputable def folkmanNativePairingAtomMatrix
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (γ : L → R → F2) :
    PrebananaAbstractAtoms (AsBoolAlg L) →
      PrebananaAbstractAtoms (AsBoolAlg R) → F2 :=
  fun a b => folkmanNativeTransportPairing γ {a} {b}

/-- The transported pairing equals its double atom-matrix sum. -/
theorem folkmanNativeTransportPairing_eq_atomMatrix
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (γ : L → R → F2)
    (hleft : ∀ x x' y, γ (x + x') y = γ x y + γ x' y)
    (hright : ∀ x y y', γ x (y + y') = γ x y + γ x y')
    (s : Finset (PrebananaAbstractAtoms (AsBoolAlg L)))
    (t : Finset (PrebananaAbstractAtoms (AsBoolAlg R))) :
    folkmanNativeTransportPairing γ s t =
      ∑ a ∈ s, ∑ b ∈ t, folkmanNativePairingAtomMatrix γ a b := by
  classical
  simpa only [folkmanNativePairingAtomMatrix] using
    (folkmanAtomPairing_eq_doubleSum
      (folkmanNativeTransportPairing γ)
      (fun x x' y => by
        convert folkmanNativeTransportPairing_add_left γ hleft x x' y using 1
          <;> first | rfl |
            (congr 1; ext z; simp only [Finset.mem_symmDiff]))
      (fun x y y' => by
        convert folkmanNativeTransportPairing_add_right γ hright x y y' using 1
          <;> first | rfl |
            (congr 1; ext z; simp only [Finset.mem_symmDiff]))
      s t)

/-- All original native ring pairing values are determined by the
two canonical atom supports and a single finite atom matrix. -/
theorem folkmanNativePairing_eq_atomMatrix
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (γ : L → R → F2)
    (hleft : ∀ x x' y, γ (x + x') y = γ x y + γ x' y)
    (hright : ∀ x y y', γ x (y + y') = γ x y + γ x y')
    (x : L) (y : R) :
    γ x y =
      ∑ a ∈ folkmanNativeRingAtomEquiv L x,
        ∑ b ∈ folkmanNativeRingAtomEquiv R y,
          folkmanNativePairingAtomMatrix γ a b := by
  calc
    γ x y =
        folkmanNativeTransportPairing γ
          (folkmanNativeRingAtomEquiv L x)
          (folkmanNativeRingAtomEquiv R y) :=
      (folkmanNativeTransportPairing_apply_codes γ x y).symm
    _ = _ :=
      folkmanNativeTransportPairing_eq_atomMatrix γ hleft hright _ _

end SuccessorTree.NonPrecompact
