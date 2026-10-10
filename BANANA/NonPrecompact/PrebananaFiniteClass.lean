import BANANA.NonPrecompact.PrebananaAmalgamBridge
import Mathlib.Data.Fintype.OfMap

/-!
# The finite pre-BANANA class: atom codes, unboundedness and the base

The standard atom presentation is a nonempty finite set of atoms,
marked by an F₂-valued function of even total parity. A one-atom,
unmarked algebra is an initial object for atom-partition embeddings:
each target atom belongs to its sole source block.

These elementary results support the joint embedding and Fraïssé
arguments for pre-BANANA, without changing the frozen manuscript.
-/

namespace SuccessorTree.NonPrecompact

/-- A finite pre-BANANA structure with n+1 unmarked atoms. -/
def prebananaUnmarked (n : ℕ) : PrebananaAtomStructure where
  atomCount := n + 1
  atomCount_pos := Nat.succ_pos n
  mark := fun _ => 0
  total_mark_parity := by
    simp [prebananaMarkedCount]

/-- The one-atom unmarked structure, which is the two-element Boolean
algebra with its mandatory zero parity. -/
def prebananaZeroBase : PrebananaAtomStructure := prebananaUnmarked 0

/-- All unmarked finite Boolean algebras belong to the pre-BANANA class,
so atom counts (and hence finite carrier sizes) are unbounded. -/
theorem prebanana_arbitrarily_many_atoms (n : ℕ) :
    ∃ A : PrebananaAtomStructure, n < A.atomCount := by
  exact ⟨prebananaUnmarked n, Nat.lt_succ_self n⟩

/-- The canonical atom map from any finite pre-BANANA structure to
the one source atom is a legitimate embedding. -/
def PrebananaAtomStructure.fromZeroBase (B : PrebananaAtomStructure) :
    PrebananaAtomEmbedding prebananaZeroBase B where
  part := fun _ => 0
  fibre_nonempty := by
    intro a
    refine ⟨B.zeroAtom, ?_⟩
    simp [prebananaFiber]
  fibre_mark_parity := by
    intro a
    simpa [prebananaZeroBase, prebananaUnmarked, prebananaFiber] using
      B.total_mark_parity

/-- Every source atom presentation has a code consisting of its
atom count and marking function. -/
def prebananaAtomCode (A : PrebananaAtomStructure) :
    Σ n : ℕ, Fin n → F2 :=
  ⟨A.atomCount, A.mark⟩

/-- The code determines the atom presentation uniquely. -/
theorem prebananaAtomCode_injective :
    Function.Injective prebananaAtomCode := by
  rintro ⟨n, hn, mark, hmark⟩ ⟨m, hm, mark', hmark'⟩ h
  cases h
  rfl

/-- There are countably many finite atom presentations, hence at
most countably many pre-BANANA isomorphism types. -/
noncomputable instance prebananaAtomStructureCountable :
    Countable PrebananaAtomStructure := by
  classical
  exact Countable.of_injective prebananaAtomCode
    prebananaAtomCode_injective

end SuccessorTree.NonPrecompact
