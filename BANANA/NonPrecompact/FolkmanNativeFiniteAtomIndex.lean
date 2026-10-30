import BANANA.NonPrecompact.FolkmanNativePairingAtomMatrix

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

open scoped Classical BigOperators

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

/-- The atom support of an original ring element, expressed with Fin labels. -/
noncomputable def folkmanNativeFinSupport
    (α : Type*) [BooleanRing α] [Fintype α] (x : α) :
    Finset (Fin (Fintype.card (PrebananaAbstractAtoms (AsBoolAlg α)))) :=
  (folkmanNativeRingAtomEquiv α x).map
    (folkmanNativeAtomFinEquiv α).toEmbedding

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
  simp only [folkmanNativeFinSupport, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact (folkmanNativeFinCode_edge γ a b).symm

end SuccessorTree.NonPrecompact
