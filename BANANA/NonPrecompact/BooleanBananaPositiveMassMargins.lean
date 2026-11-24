import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Positive integer grids with prescribed margins

Reserve one in each cell. Match the remaining row units bijectively to the
remaining column units, and count the matches in each pair of fibres.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open scoped BigOperators

private theorem card_sigma_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    (r : I → ℕ) (i : I) :
    (Finset.univ.filter (fun x : (Σ i, Fin (r i)) => x.1 = i)).card = r i := by
  have h : Finset.univ.filter (fun x : (Σ i, Fin (r i)) => x.1 = i) =
      ({i} : Finset I).sigma (fun i => (Finset.univ : Finset (Fin (r i)))) := by
    ext x
    simp
  rw [h, Finset.card_sigma]
  simp

/-- A grid with equal total margins and room for one unit in every cell
has a positive integer filling realising all prescribed row and column sums. -/
theorem exists_positive_integer_grid {I J : Type*} [Fintype I] [Fintype J]
    (r : I → ℕ) (c : J → ℕ) (hr : ∀ i, Fintype.card J ≤ r i)
    (hc : ∀ j, Fintype.card I ≤ c j) (htotal : ∑ i, r i = ∑ j, c j) :
    ∃ m : I → J → ℕ,
      (∀ i j, 0 < m i j) ∧ (∀ i, ∑ j, m i j = r i) ∧ (∀ j, ∑ i, m i j = c j) := by
  classical
  let r₀ (i : I) := r i - Fintype.card J
  let c₀ (j : J) := c j - Fintype.card I
  have hR : (∑ i, r₀ i) + Fintype.card I * Fintype.card J = ∑ i, r i := by
    calc
      _ = (∑ i, r₀ i) + ∑ _ : I, Fintype.card J := by simp [Nat.nsmul_eq_mul]
      _ = ∑ i, r i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (hr i))
  have hC : (∑ j, c₀ j) + Fintype.card J * Fintype.card I = ∑ j, c j := by
    calc
      _ = (∑ j, c₀ j) + ∑ _ : J, Fintype.card I := by simp [Nat.nsmul_eq_mul]
      _ = ∑ j, c j := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => Nat.sub_add_cancel (hc j))
  rw [Nat.mul_comm (Fintype.card J)] at hC
  have heq : (∑ i, r₀ i) = ∑ j, c₀ j := Nat.add_right_cancel (hR.trans (htotal.trans hC.symm))
  let R := Σ i, Fin (r₀ i)
  let C := Σ j, Fin (c₀ j)
  let e : R ≃ C := Fintype.equivOfCardEq (by simpa [R, C] using heq)
  let count (i : I) (j : J) :=
    (Finset.univ.filter fun x : R => x.1 = i ∧ (e x).1 = j).card
  have hrow (i : I) : (∑ j, count i j) = r₀ i := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ.filter fun x : R => x.1 = i) (Finset.univ : Finset J) (fun x => (e x).1)
    calc
      (∑ j, count i j) = (Finset.univ.filter fun x : R => x.1 = i).card := by
        simpa only [count, Finset.filter_filter, Finset.mem_univ, and_true] using h
      _ = r₀ i := card_sigma_coordinate r₀ i
  have hcol (j : J) : (∑ i, count i j) = c₀ j := by
    have h := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ.filter fun x : R => (e x).1 = j) (Finset.univ : Finset I) Sigma.fst
    have he :
        (Finset.univ.filter fun x : R => (e x).1 = j).card =
          (Finset.univ.filter fun y : C => y.1 = j).card := by
      apply Finset.card_bijective e e.bijective
      intro x
      simp
    calc
      (∑ i, count i j) = (Finset.univ.filter fun x : R => (e x).1 = j).card := by
        simpa only [count, Finset.filter_filter, Finset.mem_univ, and_true, true_and, and_comm] using h
      _ = c₀ j := he.trans (card_sigma_coordinate c₀ j)
  refine ⟨fun i j => count i j + 1, fun _ _ => Nat.succ_pos _, ?_, ?_⟩
  · intro i
    rw [Finset.sum_add_distrib, hrow]
    simpa [r₀, Nat.nsmul_eq_mul] using Nat.sub_add_cancel (hr i)
  · intro j
    rw [Finset.sum_add_distrib, hcol]
    simpa [c₀, Nat.nsmul_eq_mul] using Nat.sub_add_cancel (hc j)

end SuccessorTree.NonPrecompact.BooleanBanana
