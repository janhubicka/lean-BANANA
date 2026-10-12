import BANANA.NonPrecompact.PrebananaAbstractCodeOperations
import BANANA.NonPrecompact.PrebananaAbstractCodeParity
import BANANA.NonPrecompact.PrebananaBooleanTerms

/-!
# Boolean-term evaluation under abstract finite pre-BANANA atom codes

The canonical atom enumeration of every finite Boolean algebra sends
bottom, top, joins, meets and complements to the corresponding
operations on finite sets of atom indices. Hence it commutes with
evaluation of arbitrary Boolean terms in a distinguished tuple.

For a finite parity structure, this also identifies the F₂ mark of an
abstract term evaluation with the concrete marked-atom parity of its
coded term evaluation. This supplies the missing representation bridge
from concrete term ranges to arbitrary finite Boolean algebras in the
circulation proof. No infinite-limit orbit assertion is made.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Complements are preserved by the finite abstract atom code.
The result follows from uniqueness of complements after checking
the code preserves top, bottom, joins and meets. -/
theorem prebananaAbstractBooleanCode_compl
    (α : Type*) [BooleanAlgebra α] [Fintype α] (x : α) :
    prebananaAbstractBooleanCode α xᶜ =
      (prebananaAbstractBooleanCode α x)ᶜ := by
  classical
  let code := prebananaAbstractBooleanCode α
  have hmeet : code x ⊓ code xᶜ = ⊥ := by
    calc
      code x ⊓ code xᶜ = code (x ⊓ xᶜ) :=
        (prebananaAbstractBooleanCode_inf α x xᶜ).symm
      _ = code (⊥ : α) := by rw [inf_compl_eq_bot]
      _ = ⊥ := prebananaAbstractBooleanCode_bot α
  have hjoin : code x ⊔ code xᶜ = ⊤ := by
    calc
      code x ⊔ code xᶜ = code (x ⊔ xᶜ) :=
        (prebananaAbstractBooleanCode_sup α x xᶜ).symm
      _ = code (⊤ : α) := by rw [sup_compl_eq_top]
      _ = ⊤ := prebananaAbstractBooleanCode_top α
  exact (IsCompl.of_eq hmeet hjoin).compl_eq.symm

/-- Evaluate a Boolean term in an arbitrary Boolean algebra. -/
def PrebananaBooleanTerm.evalBoolean
    {n : ℕ} {α : Type*} [BooleanAlgebra α]
    (tuple : Fin n → α) : PrebananaBooleanTerm n → α
  | .zero => ⊥
  | .one => ⊤
  | .generator i => tuple i
  | .complement t => (evalBoolean tuple t)ᶜ
  | .join t u => evalBoolean tuple t ⊔ evalBoolean tuple u
  | .meet t u => evalBoolean tuple t ⊓ evalBoolean tuple u

/-- Encoding the interpretation of any Boolean term agrees with
evaluating the same term on the encoded tuple. -/
theorem PrebananaBooleanTerm.code_evalBoolean
    {n : ℕ} (α : Type*) [BooleanAlgebra α] [Fintype α]
    (tuple : Fin n → α) (t : PrebananaBooleanTerm n) :
    prebananaAbstractBooleanCode α (t.evalBoolean tuple) =
      t.evalSet (fun i => prebananaAbstractBooleanCode α (tuple i)) := by
  classical
  induction t with
  | zero =>
      simpa [evalBoolean, evalSet] using
        (prebananaAbstractBooleanCode_bot α)
  | one =>
      simpa [evalBoolean, evalSet] using
        (prebananaAbstractBooleanCode_top α)
  | generator i =>
      rfl
  | complement t ih =>
      simpa [evalBoolean, evalSet, prebananaAbstractBooleanCode_compl,
        Finset.compl_eq_univ_sdiff, ih]
  | join t u iht ihu =>
      simp [evalBoolean, evalSet, prebananaAbstractBooleanCode_sup,
        iht, ihu]
  | meet t u iht ihu =>
      simp [evalBoolean, evalSet, prebananaAbstractBooleanCode_inf,
        iht, ihu]

/-- The marked-atom parity of every coded Boolean term is its
original abstract parity value. -/
theorem PrebananaBooleanTerm.code_evalBoolean_parity
    {n : ℕ}
    (α : Type*) [BooleanAlgebra α] [Fintype α] [Nontrivial α]
    (μ : α → F2)
    (hzero : μ ⊥ = 0)
    (htop : μ ⊤ = 0)
    (hadd : ∀ x y : α, x ⊓ y = ⊥ →
      μ (x ⊔ y) = μ x + μ y)
    (tuple : Fin n → α) (t : PrebananaBooleanTerm n) :
    prebananaBooleanParity
      (prebananaAbstractAtomCode α μ hzero htop hadd)
      (t.evalSet (fun i => prebananaAbstractBooleanCode α (tuple i))) =
    μ (t.evalBoolean tuple) := by
  let Acode := prebananaAbstractAtomCode α μ hzero htop hadd
  let data := fun i => prebananaAbstractBooleanCode α (tuple i)
  have hcode :
      t.evalSet data = prebananaAbstractBooleanCode α (t.evalBoolean tuple) :=
    (t.code_evalBoolean α tuple).symm
  calc
    prebananaBooleanParity Acode (t.evalSet data) =
        prebananaBooleanParity Acode
          (prebananaAbstractBooleanCode α (t.evalBoolean tuple)) :=
      congrArg (prebananaBooleanParity Acode) hcode
    _ = μ (t.evalBoolean tuple) :=
      prebananaAbstractBooleanCode_parity α μ hzero htop hadd
        (t.evalBoolean tuple)

end SuccessorTree.NonPrecompact
