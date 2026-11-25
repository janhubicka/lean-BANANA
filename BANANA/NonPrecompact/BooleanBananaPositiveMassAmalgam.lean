import BANANA.NonPrecompact.BooleanBananaPositiveMassArithmetic
import BANANA.NonPrecompact.FiberProductParityAmalgam

/-!
# Positive-mass amalgams in Boolean–BANANA atom coordinates

The ordinary fibre-product atom grid admits positive rational masses with
the desired margins. The arithmetic puts a positive mass on each compatible
pair, so the existing strong-intersection result applies to the whole grid.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open scoped BigOperators

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

private theorem exists_positive_weight_grid {I J : Type*} [Fintype I] [Fintype J]
    {S : Set ℕ} {p : ℕ} (hpS : p ∈ S) (hp : p.Prime) (hpOdd : Odd p)
    (r : I → PositiveMassWeight S) (c : J → PositiveMassWeight S)
    (htotal : (∑ i, (r i).mass) = ∑ j, (c j).mass) :
    ∃ m : I → J → PositiveMassWeight S,
      (∀ i, (∑ j, (m i j).mass) = (r i).mass ∧ (∑ j, (m i j).parity) = (r i).parity) ∧
      (∀ j, (∑ i, (m i j).mass) = (c j).mass ∧ (∑ i, (m i j).parity) = (c j).parity) := by
  let w : I ⊕ J → PositiveMassWeight S := Sum.elim r c
  obtain ⟨D, u, hD, hu⟩ := exists_common_positive_mass_denominator
    (fun k => (w k).numerator) (fun k => (w k).denominator)
    (fun k => (w k).positive) (fun k => (w k).allowed)
  have hD0 : (D : ℚ) ≠ 0 := by
    obtain ⟨k, hk⟩ := hD.1
    exact_mod_cast (show D ≠ 0 by omega)
  have hR (i : I) : 0 < u (.inl i) ∧
      (u (.inl i) : ℚ) / (D : ℚ) = (r i).mass ∧ (u (.inl i) : ZMod 2) = (r i).parity :=
    hu (.inl i)
  have hC (j : J) : 0 < u (.inr j) ∧
      (u (.inr j) : ℚ) / (D : ℚ) = (c j).mass ∧ (u (.inr j) : ZMod 2) = (c j).parity :=
    hu (.inr j)
  have htotal' : (∑ i, u (.inl i)) = ∑ j, u (.inr j) := by
    have h : (∑ i, (u (.inl i) : ℚ) / (D : ℚ)) =
        ∑ j, (u (.inr j) : ℚ) / (D : ℚ) := by
      simp only [fun i => (hR i).2.1, fun j => (hC j).2.1, htotal]
    simp only [← Finset.sum_div, ← Nat.cast_sum] at h
    exact_mod_cast (div_left_inj' hD0).mp h
  obtain ⟨n, m, hmD, hm, hrow, hcol⟩ := exists_positive_mass_grid hpS hp hpOdd hD
    (fun i => u (.inl i)) (fun j => u (.inr j)) (fun i => (hR i).1) (fun j => (hC j).1) htotal'
  refine ⟨fun i j => ⟨m i j, D * p ^ n, hm i j, hmD⟩, ?_, ?_⟩
  · intro i
    exact ⟨(hrow i).1.trans (hR i).2.1, (hrow i).2.trans (hR i).2.2⟩
  · intro j
    exact ⟨(hcol j).1.trans (hC j).2.1, (hcol j).2.trans (hC j).2.2⟩

/-- The fibre-product atom grid strongly amalgamates two positive-mass
extensions. Its projections are surjective, and the mass and parity of each
old atom are the sums along its fibre. The common image of the two Boolean
powersets is exactly the base powerset. -/
theorem exists_positive_mass_strong_amalgam {A B C : Type*}
    [Fintype B] [Fintype C] [DecidableEq A]
    {S : Set ℕ} {p : ℕ} (hpS : p ∈ S) (hp : p.Prime) (hpOdd : Odd p)
    (f : B → A) (g : C → A) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (r : B → PositiveMassWeight S) (c : C → PositiveMassWeight S)
    (htotal : ∀ a : A, (∑ b : LeftFiber f a, (r b.1).mass) =
      ∑ c' : RightFiber g a, (c c'.1).mass) :
    ∃ m : FiberGrid f g → PositiveMassWeight S,
      Function.Surjective (fun x : FiberGrid f g => x.2.1.1) ∧
      Function.Surjective (fun x : FiberGrid f g => x.2.2.1) ∧
      (∀ x : FiberGrid f g, f x.2.1.1 = g x.2.2.1) ∧
      (∀ b : B,
        (∑ c' : RightFiber g (f b), (m ⟨f b, (⟨b, rfl⟩, c')⟩).mass) = (r b).mass ∧
        (∑ c' : RightFiber g (f b), (m ⟨f b, (⟨b, rfl⟩, c')⟩).parity) = (r b).parity) ∧
      (∀ c' : C,
        (∑ b : LeftFiber f (g c'), (m ⟨g c', (b, ⟨c', rfl⟩)⟩).mass) = (c c').mass ∧
        (∑ b : LeftFiber f (g c'), (m ⟨g c', (b, ⟨c', rfl⟩)⟩).parity) = (c c').parity) ∧
      ∀ (U : Set B) (V : Set C),
        (∀ x : FiberGrid f g, x.2.1.1 ∈ U ↔ x.2.2.1 ∈ V) →
        ∃ T : Set A, (∀ b, b ∈ U ↔ f b ∈ T) ∧ (∀ c', c' ∈ V ↔ g c' ∈ T) := by
  have hgrid (a : A) := exists_positive_weight_grid hpS hp hpOdd
    (fun b : LeftFiber f a => r b.1) (fun c' : RightFiber g a => c c'.1) (htotal a)
  choose w hrow hcol using hgrid
  refine ⟨fun x => w x.1 x.2.1 x.2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    exact ⟨⟨f b, (⟨b, rfl⟩, rightFiberBase g hg (f b))⟩, rfl⟩
  · intro c'
    exact ⟨⟨g c', (leftFiberBase f hf (g c'), ⟨c', rfl⟩)⟩, rfl⟩
  · exact fun x => x.2.1.2.trans x.2.2.2.symm
  · exact fun b => hrow (f b) ⟨b, rfl⟩
  · exact fun c' => hcol (g c') ⟨c', rfl⟩
  · exact exists_common_subset_of_fiberGrid f g hf hg

end SuccessorTree.NonPrecompact.BooleanBanana
