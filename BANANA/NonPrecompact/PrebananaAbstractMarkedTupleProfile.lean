import BANANA.NonPrecompact.PrebananaAbstractTermEvaluation
import BANANA.NonPrecompact.PrebananaAbstractCodeEquivalence
import BANANA.NonPrecompact.PrebananaTupleTermEqualities
import BANANA.NonPrecompact.PrebananaTupleTermParity

/-!
# Marked tuple profiles for arbitrary finite pre-BANANA Boolean structures

The concrete finite-atom profile is transported to every abstract
finite Boolean algebra by its canonical atom code. Equality of
these profiles forces the same Boolean equations among all terms,
and equality of the F₂ marking of every evaluated term.

This removes the artificial choice of a standard atom presentation
from the algebraic part of the oligomorphicity proof. It does not
formalise the infinite Fraïssé limit or the extension of finite
isomorphisms to automorphisms.
-/

namespace SuccessorTree.NonPrecompact

/-- The complete marked tuple profile of an arbitrary finite Boolean
algebra equipped with an additive F₂ marking. -/
noncomputable def prebananaAbstractMarkedTupleProfile
    (α : Type*) [BooleanAlgebra α] [Fintype α] [Nontrivial α]
    (μ : α → F2)
    (hzero : μ ⊥ = 0) (htop : μ ⊤ = 0)
    (hadd : ∀ x y : α, x ⊓ y = ⊥ →
      μ (x ⊔ y) = μ x + μ y)
    {n : ℕ} (tuple : Fin n → α) :
    Finset (Fin n → Bool) × ((Fin n → Bool) → F2) :=
  prebananaTupleProfile
    (prebananaAbstractAtomCode α μ hzero htop hadd)
    (fun i => prebananaAbstractBooleanCode α (tuple i))

/-- The complete finite tuple profile determines all Boolean-term
equations in arbitrary finite Boolean algebras, not only in their
chosen atom enumerations. -/
theorem prebananaAbstractTerm_eq_iff_of_profile_eq
    (α β : Type*)
    [BooleanAlgebra α] [Fintype α] [Nontrivial α]
    [BooleanAlgebra β] [Fintype β] [Nontrivial β]
    (μA : α → F2) (μB : β → F2)
    (hzeroA : μA ⊥ = 0) (htopA : μA ⊤ = 0)
    (haddA : ∀ x y : α, x ⊓ y = ⊥ →
      μA (x ⊔ y) = μA x + μA y)
    (hzeroB : μB ⊥ = 0) (htopB : μB ⊤ = 0)
    (haddB : ∀ x y : β, x ⊓ y = ⊥ →
      μB (x ⊔ y) = μB x + μB y)
    {n : ℕ} (tupleA : Fin n → α) (tupleB : Fin n → β)
    (hprofile :
      prebananaAbstractMarkedTupleProfile α μA hzeroA htopA haddA tupleA =
      prebananaAbstractMarkedTupleProfile β μB hzeroB htopB haddB tupleB)
    (t u : PrebananaBooleanTerm n) :
    (t.evalBoolean tupleA = u.evalBoolean tupleA) ↔
      (t.evalBoolean tupleB = u.evalBoolean tupleB) := by
  classical
  let Acode := prebananaAbstractAtomCode α μA hzeroA htopA haddA
  let Bcode := prebananaAbstractAtomCode β μB hzeroB htopB haddB
  let dataA := fun i => prebananaAbstractBooleanCode α (tupleA i)
  let dataB := fun i => prebananaAbstractBooleanCode β (tupleB i)
  have hFin :
      (t.evalSet dataA = u.evalSet dataA) ↔
        (t.evalSet dataB = u.evalSet dataB) :=
    prebananaBooleanTerm_equalities_of_profile_eq
      Acode Bcode dataA dataB hprofile t u
  constructor
  · intro heq
    have hcode : t.evalSet dataA = u.evalSet dataA := by
      calc
        t.evalSet dataA =
            prebananaAbstractBooleanCode α (t.evalBoolean tupleA) :=
          (t.code_evalBoolean α tupleA).symm
        _ = prebananaAbstractBooleanCode α (u.evalBoolean tupleA) :=
          congrArg (prebananaAbstractBooleanCode α) heq
        _ = u.evalSet dataA := u.code_evalBoolean α tupleA
    have htgt := hFin.mp hcode
    apply (prebananaAbstractBooleanCode_bijective β).1
    calc
      prebananaAbstractBooleanCode β (t.evalBoolean tupleB) =
          t.evalSet dataB := t.code_evalBoolean β tupleB
      _ = u.evalSet dataB := htgt
      _ = prebananaAbstractBooleanCode β (u.evalBoolean tupleB) :=
          (u.code_evalBoolean β tupleB).symm
  · intro heq
    have hcode : t.evalSet dataB = u.evalSet dataB := by
      calc
        t.evalSet dataB =
            prebananaAbstractBooleanCode β (t.evalBoolean tupleB) :=
          (t.code_evalBoolean β tupleB).symm
        _ = prebananaAbstractBooleanCode β (u.evalBoolean tupleB) :=
          congrArg (prebananaAbstractBooleanCode β) heq
        _ = u.evalSet dataB := u.code_evalBoolean β tupleB
    have hsrc := hFin.mpr hcode
    apply (prebananaAbstractBooleanCode_bijective α).1
    calc
      prebananaAbstractBooleanCode α (t.evalBoolean tupleA) =
          t.evalSet dataA := t.code_evalBoolean α tupleA
      _ = u.evalSet dataA := hsrc
      _ = prebananaAbstractBooleanCode α (u.evalBoolean tupleA) :=
          (u.code_evalBoolean α tupleA).symm

/-- The mark of every Boolean-term evaluation is also determined
by the complete profile of a distinguished tuple. -/
theorem prebananaAbstractTerm_mark_of_profile_eq
    (α β : Type*)
    [BooleanAlgebra α] [Fintype α] [Nontrivial α]
    [BooleanAlgebra β] [Fintype β] [Nontrivial β]
    (μA : α → F2) (μB : β → F2)
    (hzeroA : μA ⊥ = 0) (htopA : μA ⊤ = 0)
    (haddA : ∀ x y : α, x ⊓ y = ⊥ →
      μA (x ⊔ y) = μA x + μA y)
    (hzeroB : μB ⊥ = 0) (htopB : μB ⊤ = 0)
    (haddB : ∀ x y : β, x ⊓ y = ⊥ →
      μB (x ⊔ y) = μB x + μB y)
    {n : ℕ} (tupleA : Fin n → α) (tupleB : Fin n → β)
    (hprofile :
      prebananaAbstractMarkedTupleProfile α μA hzeroA htopA haddA tupleA =
      prebananaAbstractMarkedTupleProfile β μB hzeroB htopB haddB tupleB)
    (t : PrebananaBooleanTerm n) :
    μA (t.evalBoolean tupleA) = μB (t.evalBoolean tupleB) := by
  classical
  let Acode := prebananaAbstractAtomCode α μA hzeroA htopA haddA
  let Bcode := prebananaAbstractAtomCode β μB hzeroB htopB haddB
  let dataA := fun i => prebananaAbstractBooleanCode α (tupleA i)
  let dataB := fun i => prebananaAbstractBooleanCode β (tupleB i)
  have hFin :
      prebananaBooleanParity Acode (t.evalSet dataA) =
        prebananaBooleanParity Bcode (t.evalSet dataB) :=
    prebananaBooleanTerm_parity_of_profile_eq
      Acode Bcode dataA dataB hprofile t
  calc
    μA (t.evalBoolean tupleA) =
        prebananaBooleanParity Acode (t.evalSet dataA) :=
      (t.code_evalBoolean_parity α μA hzeroA htopA haddA tupleA).symm
    _ = prebananaBooleanParity Bcode (t.evalSet dataB) := hFin
    _ = μB (t.evalBoolean tupleB) :=
      t.code_evalBoolean_parity β μB hzeroB htopB haddB tupleB

end SuccessorTree.NonPrecompact
