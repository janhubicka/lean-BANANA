import BANANA.NonPrecompact.PrebananaOneGeneratorFourValues
import BANANA.NonPrecompact.PrebananaAbstractTermEvaluation

/-!
# Boolean-term normal forms for a single generator

Every Boolean term in one variable represents one of four unary
truth functions. Their values at any Boolean-algebra element x are
bottom, x, complement x, and top.

Unlike the finite-atom arguments, this theorem works in an arbitrary
Boolean algebra, including the infinite pre-BANANA Fraïssé limit.
It is the key algebraic step towards identifying the marked
one-generator subalgebras of two proper nonzero zero-marked elements,
independently of any choice of atom coordinates.

The truth function of a term is its pair of Boolean values when
the generator is false and when it is true.
-/

namespace SuccessorTree.NonPrecompact

/-- The four possible unary Boolean truth functions evaluated at x,
indexed by their truth values at false and true. -/
def prebananaUnaryTruthValue
    {α : Type*} [BooleanAlgebra α] (x : α) :
    Bool → Bool → α
  | false, false => ⊥
  | false, true => x
  | true, false => xᶜ
  | true, true => ⊤

/-- Complementation of unary truth functions corresponds to
Boolean complementation of their values at any x. -/
theorem prebananaUnaryTruthValue_complement
    {α : Type*} [BooleanAlgebra α]
    (x : α) (a b : Bool) :
    prebananaUnaryTruthValue x (!a) (!b) =
      (prebananaUnaryTruthValue x a b)ᶜ := by
  cases a <;> cases b <;>
    simp [prebananaUnaryTruthValue, compl_compl]

/-- Pointwise joins of two unary truth functions are joins
of their evaluated Boolean-algebra values. -/
theorem prebananaUnaryTruthValue_join
    {α : Type*} [BooleanAlgebra α]
    (x : α) (a b c d : Bool) :
    prebananaUnaryTruthValue x (a || c) (b || d) =
      prebananaUnaryTruthValue x a b ⊔
        prebananaUnaryTruthValue x c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [prebananaUnaryTruthValue, sup_compl_eq_top, compl_sup_eq_top,
      sup_comm]

/-- Pointwise meets of two unary truth functions are meets
of their evaluated Boolean-algebra values. -/
theorem prebananaUnaryTruthValue_meet
    {α : Type*} [BooleanAlgebra α]
    (x : α) (a b c d : Bool) :
    prebananaUnaryTruthValue x (a && c) (b && d) =
      prebananaUnaryTruthValue x a b ⊓
        prebananaUnaryTruthValue x c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [prebananaUnaryTruthValue, inf_compl_eq_bot, compl_inf_eq_bot,
      inf_comm]

/-- A one-variable Boolean term has the same value as the unary
truth function determined by its two Boolean evaluations. This
normal form is independent of the ambient Boolean algebra. -/
theorem PrebananaBooleanTerm.oneGenerator_truthTable
    {α : Type*} [BooleanAlgebra α]
    (x : α) (t : PrebananaBooleanTerm 1) :
    t.evalBoolean (fun _ : Fin 1 => x) =
      prebananaUnaryTruthValue x
        (t.evalPattern (fun _ : Fin 1 => false))
        (t.evalPattern (fun _ : Fin 1 => true)) := by
  induction t with
  | zero =>
      rfl
  | one =>
      rfl
  | generator i =>
      fin_cases i
      rfl
  | complement t ih =>
      change (t.evalBoolean (fun _ : Fin 1 => x))ᶜ =
        prebananaUnaryTruthValue x
          (!(t.evalPattern (fun _ : Fin 1 => false)))
          (!(t.evalPattern (fun _ : Fin 1 => true)))
      rw [ih]
      exact (prebananaUnaryTruthValue_complement x _ _).symm
  | join t u iht ihu =>
      change t.evalBoolean (fun _ : Fin 1 => x) ⊔
          u.evalBoolean (fun _ : Fin 1 => x) =
        prebananaUnaryTruthValue x
          (t.evalPattern (fun _ : Fin 1 => false) ||
            u.evalPattern (fun _ : Fin 1 => false))
          (t.evalPattern (fun _ : Fin 1 => true) ||
            u.evalPattern (fun _ : Fin 1 => true))
      rw [iht, ihu]
      exact (prebananaUnaryTruthValue_join x _ _ _ _).symm
  | meet t u iht ihu =>
      change t.evalBoolean (fun _ : Fin 1 => x) ⊓
          u.evalBoolean (fun _ : Fin 1 => x) =
        prebananaUnaryTruthValue x
          (t.evalPattern (fun _ : Fin 1 => false) &&
            u.evalPattern (fun _ : Fin 1 => false))
          (t.evalPattern (fun _ : Fin 1 => true) &&
            u.evalPattern (fun _ : Fin 1 => true))
      rw [iht, ihu]
      exact (prebananaUnaryTruthValue_meet x _ _ _ _).symm

end SuccessorTree.NonPrecompact
