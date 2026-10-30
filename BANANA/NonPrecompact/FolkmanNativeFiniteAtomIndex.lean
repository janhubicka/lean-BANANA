import BANANA.NonPrecompact.FolkmanNativePairingAtomMatrix
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Image

/-!
# Fin-indexed presentation of an arbitrary native Folkman pairing

For any two *finite native Boolean rings*, the canonical atom coordinates
may be enumerated by finite types.  The resulting pair of finite atom
counts and their F₂-matrix form an existing FolkmanAtomStructure.

The original native pairing is recovered from this Fin-indexed matrix
on the indexed supports of arbitrary original ring elements.  This
works when either original ring is the one-element zero ring, and
requires no unitality assumption on embeddings.

Only the finite-object isomorphism-type bridge is addressed here:
packaging the hereditary, JEP and strong-AP results into a class-level
Fraïssé theorem and building the limit are separate tasks.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff BigOperators

local instance folkmanAsBoolAlgFiniteForFinIndex
    (α : Type*) [Fintype α] : Fintype (AsBoolAlg α) :=
  Fintype.ofEquiv α toBoolAlg

/-- Choose finite labels for the atoms of an arbitrary finite Boolean ring.
The zero ring has an empty atom type and is assigned Fin 0. -/
noncomputable def folkmanNativeAtomFinEquiv
    (α : Type*) [BooleanRing α] [Fintype α] :
    PrebananaAbstractAtoms (AsBoolAlg α) ≃
      Fin (Fintype.card (PrebananaAbstractAtoms (AsBoolAlg α))) := by
  classical
  exact Fintype.equivFin _

/-- A bijection between a native finite Boolean ring and the finite
powerset ring on an explicitly numbered atom set. The following lemmas
verify the original ring operations, so this is a ring isomorphism in
the manuscript's non-unital language. -/
noncomputable def folkmanNativeFiniteRingCodeEquiv
    (α : Type*) [BooleanRing α] [Fintype α] :
    α ≃ Finset (Fin (Fintype.card (PrebananaAbstractAtoms (AsBoolAlg α)))) :=
  (folkmanNativeRingAtomEquiv α).trans
    (folkmanNativeAtomFinEquiv α).finsetCongr

/-- The original zero element corresponds to an empty atom support. -/
theorem folkmanNativeFiniteRingCode_zero
    (α : Type*) [BooleanRing α] [Fintype α] :
    folkmanNativeFiniteRingCodeEquiv α (0 : α) = ∅ := by
  classical
  simp [folkmanNativeFiniteRingCodeEquiv, folkmanNativeRingAtomEquiv_zero]

/-- Native multiplication is intersection of indexed atom supports. -/
theorem folkmanNativeFiniteRingCode_mul
    (α : Type*) [BooleanRing α] [Fintype α] (x y : α) :
    folkmanNativeFiniteRingCodeEquiv α (x * y) =
      folkmanNativeFiniteRingCodeEquiv α x ∩
        folkmanNativeFiniteRingCodeEquiv α y := by
  classical
  simp only [folkmanNativeFiniteRingCodeEquiv, Equiv.trans_apply,
    Equiv.finsetCongr_apply, folkmanNativeRingAtomEquiv_mul,
    Finset.map_inter]

/-- Native addition is symmetric difference of indexed atom supports. -/
theorem folkmanNativeFiniteRingCode_add
    (α : Type*) [BooleanRing α] [Fintype α] (x y : α) :
    folkmanNativeFiniteRingCodeEquiv α (x + y) =
      symmDiff (folkmanNativeFiniteRingCodeEquiv α x)
        (folkmanNativeFiniteRingCodeEquiv α y) := by
  classical
  ext i
  simp only [folkmanNativeFiniteRingCodeEquiv, Equiv.trans_apply,
    Equiv.finsetCongr_apply, folkmanNativeRingAtomEquiv_add,
    Finset.mem_map_equiv, Finset.mem_symmDiff]

/-- The atom support of an original ring element, expressed with Fin labels. -/
noncomputable def folkmanNativeFinSupport
    (α : Type*) [BooleanRing α] [Fintype α] (x : α) :
    Finset (Fin (Fintype.card (PrebananaAbstractAtoms (AsBoolAlg α)))) :=
  folkmanNativeFiniteRingCodeEquiv α x

/-- A finite native Folkman pairing in the existing Fin-atom presentation.
No nonzero or unitality hypotheses are used. -/
noncomputable def folkmanNativeFinCode
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (γ : L → R → F2) : FolkmanAtomStructure where
  leftCount := Fintype.card (PrebananaAbstractAtoms (AsBoolAlg L))
  rightCount := Fintype.card (PrebananaAbstractAtoms (AsBoolAlg R))
  edge := fun i j =>
    folkmanNativePairingAtomMatrix γ
      ((folkmanNativeAtomFinEquiv L).symm i)
      ((folkmanNativeAtomFinEquiv R).symm j)

/-- The indexed matrix has the original atom-to-atom pairing entries. -/
theorem folkmanNativeFinCode_edge
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (γ : L → R → F2)
    (a : PrebananaAbstractAtoms (AsBoolAlg L))
    (b : PrebananaAbstractAtoms (AsBoolAlg R)) :
    (folkmanNativeFinCode γ).edge
      (folkmanNativeAtomFinEquiv L a)
      (folkmanNativeAtomFinEquiv R b) =
      folkmanNativePairingAtomMatrix γ a b := by
  simp only [folkmanNativeFinCode, Equiv.symm_apply_apply]

/-- Reconstruction on *actual original ring elements*: the native pairing
is exactly the double sum of the corresponding Fin-indexed atom-matrix
entries.  This supplies the canonical finite-presentation bridge needed
for counting finite Folkman isomorphism types. -/
theorem folkmanNativeFinCode_pairing
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (γ : L → R → F2)
    (hleft : ∀ x x' y, γ (x + x') y = γ x y + γ x' y)
    (hright : ∀ x y y', γ x (y + y') = γ x y + γ x y')
    (x : L) (y : R) :
    γ x y =
      ∑ i ∈ folkmanNativeFinSupport L x,
        ∑ j ∈ folkmanNativeFinSupport R y,
          (folkmanNativeFinCode γ).edge i j := by
  classical
  rw [folkmanNativePairing_eq_atomMatrix γ hleft hright x y]
  simp only [folkmanNativeFinSupport, folkmanNativeFiniteRingCodeEquiv,
    Equiv.trans_apply, Equiv.finsetCongr_apply, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact (folkmanNativeFinCode_edge γ a b).symm


/-- Every finite native two-sort Folkman object has a fully faithful
finite-index presentation: ring addition, ring multiplication, zeros
and every value of the original pairing are preserved.

Together with countability of FolkmanAtomStructure, this is the
finite-object isomorphism-type step for the Fraïssé-class argument.
It is independent of strong amalgamation and of the limit construction. -/
theorem folkmanNative_exists_finite_index_presentation
    {L R : Type*}
    [BooleanRing L] [Fintype L]
    [BooleanRing R] [Fintype R]
    (γ : L → R → F2)
    (hleft : ∀ x x' y, γ (x + x') y = γ x y + γ x' y)
    (hright : ∀ x y y', γ x (y + y') = γ x y + γ x y') :
    ∃ A : FolkmanAtomStructure,
      ∃ eL : L ≃ Finset (Fin A.leftCount),
        ∃ eR : R ≃ Finset (Fin A.rightCount),
          (∀ x : L, ∀ y : R,
            γ x y = ∑ i ∈ eL x, ∑ j ∈ eR y, A.edge i j) ∧
          (∀ x x' : L, eL (x + x') = symmDiff (eL x) (eL x')) ∧
          (∀ y y' : R, eR (y + y') = symmDiff (eR y) (eR y')) ∧
          (∀ x x' : L, eL (x * x') = eL x ∩ eL x') ∧
          (∀ y y' : R, eR (y * y') = eR y ∩ eR y') ∧
          eL (0 : L) = ∅ ∧ eR (0 : R) = ∅ := by
  classical
  refine ⟨folkmanNativeFinCode γ,
    folkmanNativeFiniteRingCodeEquiv L,
    folkmanNativeFiniteRingCodeEquiv R, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact folkmanNativeFinCode_pairing γ hleft hright x y
  · intro x x'
    exact folkmanNativeFiniteRingCode_add L x x'
  · intro y y'
    exact folkmanNativeFiniteRingCode_add R y y'
  · intro x x'
    exact folkmanNativeFiniteRingCode_mul L x x'
  · intro y y'
    exact folkmanNativeFiniteRingCode_mul R y y'
  · exact folkmanNativeFiniteRingCode_zero L
  · exact folkmanNativeFiniteRingCode_zero R

end SuccessorTree.NonPrecompact
