import BANANA.NonPrecompact.PrebananaFiveAryChildMarking
import Mathlib

/-!
# Numerical descendant bounds for the five-ary pre-BANANA tower

The one-step marking rule has two permanently marked children and
one child inheriting its parent's mark. At a depth k below a fixed
parent, the number of marked descendants therefore follows
M(0)=0 or 1, M(k+1)=2*5^k+M(k).

This module formalises the arithmetic recurrence and a uniform
lower bound on both sorts of descendants. It does not yet identify
these numerical counts with the fibres of a constructed word tower.
That identification is a separate formalisation obligation.
-/

namespace SuccessorTree.NonPrecompact

/-- The numerical recurrence for the number of marked descendants
of a parent carrying the given initial marking. -/
def prebananaFiveAryMarkedDescendantCount (p : F2) : ℕ → ℕ
  | 0 => if p = 0 then 0 else 1
  | k + 1 => 2 * 5 ^ k + prebananaFiveAryMarkedDescendantCount p k

/-- The numerical recurrence for unmarked descendants.
Complementing the parent's F₂ mark interchanges the two counts. -/
def prebananaFiveAryUnmarkedDescendantCount (p : F2) (k : ℕ) : ℕ :=
  prebananaFiveAryMarkedDescendantCount (p + 1) k

/-- A parent of either parity has at least 2k marked descendants at
depth k. The recurrence is the only required arithmetic input. -/
theorem prebananaFiveAryMarkedDescendantCount_lower (p : F2) (k : ℕ) :
    2 * k ≤ prebananaFiveAryMarkedDescendantCount p k := by
  induction k with
  | zero =>
      simp [prebananaFiveAryMarkedDescendantCount]
  | succ k ih =>
      have hpow : 0 < 5 ^ k := by positivity
      change 2 * (k + 1) ≤
        2 * 5 ^ k + prebananaFiveAryMarkedDescendantCount p k
      omega

/-- The same uniform lower bound holds for unmarked descendants. -/
theorem prebananaFiveAryUnmarkedDescendantCount_lower (p : F2) (k : ℕ) :
    2 * k ≤ prebananaFiveAryUnmarkedDescendantCount p k := by
  exact prebananaFiveAryMarkedDescendantCount_lower (p + 1) k

end SuccessorTree.NonPrecompact
