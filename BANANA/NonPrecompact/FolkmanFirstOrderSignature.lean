import Mathlib.ModelTheory.Fraisse

/-!
# A finite first-order signature for the two-sorted Folkman pairing

The finite original-language Folkman structure has two ring sorts,
each with a named zero, addition and multiplication, and an
F₂-valued pairing from the left to the right sort.

For a single-sorted Fraïssé existence theorem, the proposed
carrier is the disjoint sum of the two sorts. The two unary
relations distinguish the summands. Wrong-sort arguments of
each ring operation will be totalised to the zero of the
corresponding output sort; the pairing-one relation is false
outside left × right.

There are exactly two nullary functions, four binary functions,
two unary relations and one binary relation. No multiplicative
identity is named. This module ONLY specifies the finite
signature and its symbol countability: faithful interpretations,
embeddings and native-class equivalence remain separate
Lean implementation obligations.

The pinned Mathlib Fraïssé API requires countably many
function symbols. The signature below meets that prerequisite.
This source is draft until an exact-head local Lean build.
-/

namespace SuccessorTree.NonPrecompact

/-- Constants: left/right zero. Binary operations: addition and
multiplication on each of the two original ring sorts. -/
def folkmanFirstOrderFunctions (n : ℕ) : Type :=
  if n = 0 then Fin 2
  else if n = 2 then Fin 4
  else Empty

/-- Two unary sort predicates, and one binary predicate recording
whether the original F₂ pairing has value one. -/
def folkmanFirstOrderRelations (n : ℕ) : Type :=
  if n = 1 then Fin 2
  else if n = 2 then PUnit
  else Empty

/-- Every individual function-symbol arity has finitely many
symbols, including the empty arities. -/
noncomputable instance folkmanFirstOrderFunctionsFintype (n : ℕ) :
    Fintype (folkmanFirstOrderFunctions n) := by
  unfold folkmanFirstOrderFunctions
  split_ifs <;> infer_instance

/-- The relation-symbol type is finite in each arity as well. -/
noncomputable instance folkmanFirstOrderRelationsFintype (n : ℕ) :
    Fintype (folkmanFirstOrderRelations n) := by
  unfold folkmanFirstOrderRelations
  split_ifs <;> infer_instance

/-- A finite-language encoding of the exact non-unital Folkman
signature with two original sorts. -/
def folkmanFirstOrderLanguage : FirstOrder.Language where
  Functions := folkmanFirstOrderFunctions
  Relations := folkmanFirstOrderRelations

/-- In particular, the function-symbol countability assumption
of the classical Fraïssé existence theorem is satisfied. -/
noncomputable instance folkmanFirstOrderFunctionSymbolsCountable :
    Countable (Σ n, folkmanFirstOrderLanguage.Functions n) := by
  change Countable (Σ n, folkmanFirstOrderFunctions n)
  infer_instance

end SuccessorTree.NonPrecompact
