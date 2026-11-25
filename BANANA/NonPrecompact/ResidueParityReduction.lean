import Mathlib.Data.ZMod.Basic

namespace SuccessorTree.NonPrecompact

/-- Reduction modulo two from a power-of-two residue ring. -/
def residueParityHom (k : ℕ) :
    ZMod (2 ^ (k + 1)) →+* ZMod 2 :=
  ZMod.castHom
    (dvd_pow_self 2 (Nat.succ_ne_zero k))
    (ZMod 2)

end SuccessorTree.NonPrecompact
