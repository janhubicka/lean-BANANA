import BANANA.NonPrecompact.BananaLimitTupleSignatures
import BANANA.NonPrecompact.BananaLimitBilinearity

/-!
# Pairings of linear combinations in the explicit BANANA limit

For fixed finite tuples on each sort, the pairing of any two linear
combinations is determined by the rectangular table of pairings of
tuple entries. This is the algebraic step needed to prove that the
finite tuple signature from the manuscript is a complete orbit
invariant.

The calculation uses linear-functional wrappers from the verified
bilinearity module, rather than expanding finite supports directly.
-/

namespace SuccessorTree.NonPrecompact

/-- Evaluate the pairing of a linear combination in the left sort. -/
theorem bananaLimitPairing_tupleCombination_left {l : ℕ}
    (a : Fin l → BananaLimitVector) (c : Fin l → F2)
    (y : BananaLimitVector) :
    bananaLimitPairing (bananaLimitTupleCombination a c) y =
      ∑ i : Fin l, c i * bananaLimitPairing (a i) y := by
  classical
  rw [bananaLimitTupleCombination, Fintype.linearCombination_apply]
  change (bananaLimitPairingLeftLinear y) (∑ i : Fin l, c i • a i) =
    ∑ i : Fin l, c i * bananaLimitPairing (a i) y
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

/-- Evaluate the pairing of a linear combination in the right sort. -/
theorem bananaLimitPairing_tupleCombination_right {r : ℕ}
    (b : Fin r → BananaLimitVector) (d : Fin r → F2)
    (x : BananaLimitVector) :
    bananaLimitPairing x (bananaLimitTupleCombination b d) =
      ∑ j : Fin r, d j * bananaLimitPairing x (b j) := by
  classical
  rw [bananaLimitTupleCombination, Fintype.linearCombination_apply]
  change (bananaLimitPairingRightLinear x) (∑ j : Fin r, d j • b j) =
    ∑ j : Fin r, d j * bananaLimitPairing x (b j)
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

/-- Finite bilinearity: the table of pairings of tuple entries
determines all pairings between their linear combinations. -/
theorem bananaLimitPairing_tupleCombinations {l r : ℕ}
    (a : Fin l → BananaLimitVector)
    (b : Fin r → BananaLimitVector)
    (c : Fin l → F2) (d : Fin r → F2) :
    bananaLimitPairing
        (bananaLimitTupleCombination a c)
        (bananaLimitTupleCombination b d) =
      ∑ i : Fin l, c i *
        (∑ j : Fin r, d j * bananaLimitPairing (a i) (b j)) := by
  rw [bananaLimitPairing_tupleCombination_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [bananaLimitPairing_tupleCombination_right]

/-- Two pairs of tuples with the same pairing table have identical
pairings for every pair of coefficient vectors, even when the
individual tuple entries satisfy linear relations. -/
theorem bananaLimitPairing_tupleCombinations_eq_of_entries {l r : ℕ}
    (a a' : Fin l → BananaLimitVector)
    (b b' : Fin r → BananaLimitVector)
    (h : ∀ i j, bananaLimitPairing (a i) (b j) =
      bananaLimitPairing (a' i) (b' j))
    (c : Fin l → F2) (d : Fin r → F2) :
    bananaLimitPairing
        (bananaLimitTupleCombination a c)
        (bananaLimitTupleCombination b d) =
      bananaLimitPairing
        (bananaLimitTupleCombination a' c)
        (bananaLimitTupleCombination b' d) := by
  rw [bananaLimitPairing_tupleCombinations,
    bananaLimitPairing_tupleCombinations]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [h i j]

end SuccessorTree.NonPrecompact
