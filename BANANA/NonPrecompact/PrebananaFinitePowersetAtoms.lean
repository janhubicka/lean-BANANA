import BANANA.NonPrecompact.PrebananaFiveAryBooleanStage
import BANANA.NonPrecompact.PrebananaFiniteBooleanRepresentation
import Mathlib.Data.Finset.Grade

/-!
# Atoms of an actual finite powerset and their word markings

Finite marked Boolean algebras are represented using their abstract
atoms, whereas the five-ary tower uses its literal word atoms.
A Boolean atom of `Finset ι` is precisely a singleton, so these
two presentations are canonically equivalent.

This conversion is an algebraic bridge for the eventual
finite-extension theorem over arbitrary finite marked Boolean
algebras. It is not yet that full extension theorem.
-/

namespace SuccessorTree.NonPrecompact

/-- Canonical correspondence between abstract atoms of the Boolean
powerset of a finite type and the underlying individual atoms. -/
noncomputable def prebananaFinitePowersetAtomEquiv
    (ι : Type*) [Fintype ι] :
    PrebananaAbstractAtoms (Finset ι) ≃ ι := by
  classical
  refine
    { toFun := fun a => Classical.choose (Finset.isAtom_iff.mp a.property)
      invFun := fun i => ⟨{i}, Finset.isAtom_singleton i⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro a
    apply Subtype.ext
    exact (Classical.choose_spec (Finset.isAtom_iff.mp a.property)).symm
  · intro i
    have h := Classical.choose_spec
      (Finset.isAtom_iff.mp (Finset.isAtom_singleton i))
    exact (Finset.singleton_inj.mp h).symm

/-- Every abstract atom of a finite powerset is literally its
corresponding singleton. -/
theorem prebananaFinitePowersetAtom_eq_singleton
    (ι : Type*) [Fintype ι]
    (a : PrebananaAbstractAtoms (Finset ι)) :
    (a : Finset ι) = {prebananaFinitePowersetAtomEquiv ι a} := by
  classical
  change (a : Finset ι) =
    {Classical.choose (Finset.isAtom_iff.mp a.property)}
  exact Classical.choose_spec (Finset.isAtom_iff.mp a.property)

/-- Under this correspondence, the marking of an abstract atom
in the actual five-ary Boolean stage is exactly the mark of its
unique word. -/
theorem prebananaFiveAryStageAtom_mark (n : ℕ)
    (a : PrebananaAbstractAtoms
      (Finset (PrebananaFiveAryWord n))) :
    (prebananaFiveAryBooleanStage n).μ (a : Finset (PrebananaFiveAryWord n)) =
      prebananaFiveAryWordMark n
        (prebananaFinitePowersetAtomEquiv (PrebananaFiveAryWord n) a) := by
  classical
  change
    (∑ w ∈ (a : Finset (PrebananaFiveAryWord n)),
      prebananaFiveAryWordMark n w) =
      prebananaFiveAryWordMark n
        (prebananaFinitePowersetAtomEquiv (PrebananaFiveAryWord n) a)
  rw [prebananaFinitePowersetAtom_eq_singleton]
  simp

/-- The F₂-marked fibre sum is unchanged when one replaces
the abstract atoms of a word powerset by the actual word atoms. -/
theorem prebananaFiveAryStageAtom_fibreSum
    (n : ℕ) (δ : Type*) [DecidableEq δ]
    (part : PrebananaAbstractAtoms
      (Finset (PrebananaFiveAryWord n)) → δ)
    (d : δ) :
    (∑ w : PrebananaFiveAryWord n,
      if part ((prebananaFinitePowersetAtomEquiv
          (PrebananaFiveAryWord n)).symm w) = d then
        prebananaFiveAryWordMark n w else 0) =
    ∑ a : PrebananaAbstractAtoms (Finset (PrebananaFiveAryWord n)),
      if part a = d then
        (prebananaFiveAryBooleanStage n).μ
          (a : Finset (PrebananaFiveAryWord n)) else 0 := by
  classical
  let e := prebananaFinitePowersetAtomEquiv (PrebananaFiveAryWord n)
  symm
  exact Fintype.sum_equiv e
    (fun a =>
      if part a = d then
        (prebananaFiveAryBooleanStage n).μ
          (a : Finset (PrebananaFiveAryWord n)) else 0)
    (fun w =>
      if part (e.symm w) = d then prebananaFiveAryWordMark n w else 0)
    (by
      intro a
      have hm := prebananaFiveAryStageAtom_mark n a
      by_cases h : part a = d
      · simp only [e.symm_apply_apply, h, ite_true]
        exact hm
      · simp only [e.symm_apply_apply, h, ite_false])

end SuccessorTree.NonPrecompact
