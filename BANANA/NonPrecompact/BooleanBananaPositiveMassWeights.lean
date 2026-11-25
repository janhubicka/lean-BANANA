import BANANA.NonPrecompact.BooleanBananaPositiveMassArithmetic

/-! The common positive-mass atom weight interface. -/

namespace SuccessorTree.NonPrecompact.BooleanBanana

/-- A positive rational weight presented over an allowed odd denominator. -/
structure PositiveMassWeight (S : Set ℕ) where
  numerator : ℕ
  denominator : ℕ
  positive : 0 < numerator
  allowed : denominator ∈ positiveMassDenominators S

def PositiveMassWeight.mass {S : Set ℕ} (w : PositiveMassWeight S) : ℚ :=
  (w.numerator : ℚ) / (w.denominator : ℚ)

def PositiveMassWeight.parity {S : Set ℕ} (w : PositiveMassWeight S) : ZMod 2 :=
  w.numerator

end SuccessorTree.NonPrecompact.BooleanBanana
