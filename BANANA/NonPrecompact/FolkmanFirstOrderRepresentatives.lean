import BANANA.NonPrecompact.FolkmanFirstOrderGeneratedClosure
import BANANA.NonPrecompact.FolkmanNativeFiniteCodeRealisation
import BANANA.NonPrecompact.FolkmanFiniteClassData

/-!
# Finite tagged first-order representatives for Folkman--BANANA

Every finite atom matrix A gives a genuine finite native Folkman
pairing on two Boolean-ring powerset carriers. Encode those two
carriers in the finite single-sorted tagged language, preserving
the zero/addition/multiplication operations and the FULL pairing
relation, with no named multiplicative identities.

The family is indexed by FolkmanAtomStructure, which the existing
finite-class theorem proves is countable. Each representative has
a finite (hence countable, finitely generated) carrier. There is
a zero/zero representative, so the index family is inhabited.

These are the basic input TYPES required by the external verified
classical Fraisse-sequence theorem. Heredity, joint embedding and
amalgamation must still be transferred to first-order embeddings
using the faithful adapter. No countable limit is asserted here.
-/

namespace SuccessorTree.NonPrecompact

open scoped FirstOrder

/-- An actual tagged finite first-order structure representing
the original native Folkman atom matrix in both ring sorts. -/
noncomputable def folkmanFirstOrderRepresentative
    (A : FolkmanAtomStructure) :
    CategoryTheory.Bundled.{0} folkmanFirstOrderLanguage.Structure :=
  ⟨Sum (FolkmanNativeCodeRing A.leftCount)
       (FolkmanNativeCodeRing A.rightCount),
    folkmanTaggedFirstOrderStructure
      (FolkmanNativeCodeRing A.leftCount)
      (FolkmanNativeCodeRing A.rightCount)
      (folkmanNativeCodeRealisation A).pairing⟩

/-- Every representative has a finite tagged carrier, including
when one or both Boolean-ring sorts consist solely of zero. -/
noncomputable instance folkmanFirstOrderRepresentativeFinite
    (A : FolkmanAtomStructure) :
    Finite (folkmanFirstOrderRepresentative A) := by
  change Finite
    (Sum (FolkmanNativeCodeRing A.leftCount)
      (FolkmanNativeCodeRing A.rightCount))
  infer_instance

/-- Every finite tagged representative is also countable. -/
noncomputable instance folkmanFirstOrderRepresentativeCountable
    (A : FolkmanAtomStructure) :
    Countable (folkmanFirstOrderRepresentative A) := by
  infer_instance

/-- A finite carrier in a finite first-order language is finitely
generated: its entire carrier is a finite generating set. -/
theorem folkmanFirstOrderRepresentative_fg
    (A : FolkmanAtomStructure) :
    FirstOrder.Language.Structure.FG folkmanFirstOrderLanguage
      (folkmanFirstOrderRepresentative A) := by
  exact FirstOrder.Language.Structure.fg_iff_finite.mpr inferInstance

/-- The index of all finite Folkman atom matrices is inhabited,
including the pair of zero rings and its empty pairing matrix. -/
instance folkmanFirstOrderRepresentativeIndexNonempty :
    Nonempty FolkmanAtomStructure :=
  ⟨FolkmanAtomStructure.zeroPairing 0 0⟩

/-- The same indexed family has only countably many representatives
(no uniqueness of codes or atom numberings is required). -/
noncomputable instance folkmanFirstOrderRepresentativeIndexCountable :
    Countable FolkmanAtomStructure := by
  infer_instance

end SuccessorTree.NonPrecompact
