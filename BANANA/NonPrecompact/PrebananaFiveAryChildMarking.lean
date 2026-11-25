import BANANA.NonPrecompact.PrebananaFiniteBooleanTower
import Mathlib.Tactic.NormNum
import BANANA.NonPrecompact.PrebananaFiveAryWordBasics

/-!
# The five-ary atom-splitting parity rule

To construct an explicit pre-BANANA Fraïssé limit, every finite
atom is replaced by five children. Regardless of the parent's
mark p ∈ F₂, two children have mark zero, two have mark one,
and the last inherits p.

This module isolates the one-step parity rule. The infinite tower,
its finite extension property, and its ultrahomogeneous limit
are separate outstanding obligations.
-/
