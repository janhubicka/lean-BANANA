import BANANA.NonPrecompact.PrebananaPowersetBridge
import Mathlib.Tactic

/-!
# The finitely additive measure obstruction to pre-BANANA amenability

The circulated non-amenability argument uses the space of ultrafilters
of the underlying Boolean algebra. An invariant probability measure
there yields a finitely additive probability mass on Boolean elements.

All nonzero proper parity-zero elements of the countable Fraïssé limit
are in one orbit. If there are partitions of the unit into two and
into three such elements, finite additivity forces simultaneously
2t = 1 and 3t = 1, which is impossible.

This module proves the exact algebraic contradiction for a Boolean
algebra with a group action. It does not claim that the Fraïssé limit,
its automorphism group, Stone space, or orbit-transitivity statement
has itself been constructed in Lean.
-/

namespace SuccessorTree.NonPrecompact

/-- The family of proper, nonzero, unmarked Boolean elements. -/
def prebananaProperZeroMark
    {α : Type*} [BooleanAlgebra α]
    (μ : α → F2) (x : α) : Prop :=
  x ≠ ⊥ ∧ x ≠ ⊤ ∧ μ x = 0

/-- No finitely additive mass on a Boolean algebra can assign
one common value to every proper nonzero zero-marked element if
the unit admits disjoint partitions into two and three of them. -/
theorem prebanana_no_uniformMass_two_three
    {α : Type*} [BooleanAlgebra α]
    (μ : α → F2) (mass : α → ℝ)
    (hadd : ∀ x y : α, x ⊓ y = ⊥ →
      mass (x ⊔ y) = mass x + mass y)
    (hunit : mass ⊤ = 1)
    (hequal : ∀ x y : α,
      prebananaProperZeroMark μ x →
      prebananaProperZeroMark μ y →
      mass x = mass y)
    (a b c d e : α)
    (ha : prebananaProperZeroMark μ a)
    (hb : prebananaProperZeroMark μ b)
    (hc : prebananaProperZeroMark μ c)
    (hd : prebananaProperZeroMark μ d)
    (he : prebananaProperZeroMark μ e)
    (hab : a ⊓ b = ⊥)
    (habtop : a ⊔ b = ⊤)
    (hcd : c ⊓ d = ⊥)
    (hce : c ⊓ e = ⊥)
    (hde : d ⊓ e = ⊥)
    (hcdetop : (c ⊔ d) ⊔ e = ⊤) :
    False := by
  have ht : (c ⊔ d) ⊓ e = ⊥ := by
    rw [sup_inf_right, hce, hde]
    simp
  have htwo : mass a + mass b = 1 := by
    calc
      mass a + mass b = mass (a ⊔ b) := (hadd a b hab).symm
      _ = 1 := by rw [habtop, hunit]
  have hthree : mass c + mass d + mass e = 1 := by
    calc
      mass c + mass d + mass e =
          mass (c ⊔ d) + mass e := by rw [hadd c d hcd]
      _ = mass ((c ⊔ d) ⊔ e) :=
        (hadd (c ⊔ d) e ht).symm
      _ = 1 := by rw [hcdetop, hunit]
  have hbmass := hequal b a hb ha
  have hcmass := hequal c a hc ha
  have hdmass := hequal d a hd ha
  have hemass := hequal e a he ha
  rw [hbmass] at htwo
  rw [hcmass, hdmass, hemass] at hthree
  linarith

/-- Orbit transitivity and invariance of a mass imply that its
values agree on all proper nonzero zero-marked Boolean elements. -/
theorem prebanana_invariantMass_constant_on_zeroMark_orbit
    {α G : Type*}
    [BooleanAlgebra α] [Group G] [MulAction G α]
    (μ : α → F2) (mass : α → ℝ)
    (htrans : ∀ x y : α,
      prebananaProperZeroMark μ x →
      prebananaProperZeroMark μ y →
      ∃ g : G, g • x = y)
    (hinv : ∀ g : G, ∀ x : α, mass (g • x) = mass x)
    (x y : α)
    (hx : prebananaProperZeroMark μ x)
    (hy : prebananaProperZeroMark μ y) :
    mass x = mass y := by
  obtain ⟨g, hg⟩ := htrans x y hx hy
  calc
    mass x = mass (g • x) := (hinv g x).symm
    _ = mass y := congrArg mass hg

/-- The abstract measure-theoretic core of the pre-BANANA
non-amenability proof, conditional only on the two finite
partitions, orbit transitivity, and invariant finite additivity. -/
theorem prebanana_no_invariantMass_of_zeroMark_orbit
    {α G : Type*}
    [BooleanAlgebra α] [Group G] [MulAction G α]
    (μ : α → F2) (mass : α → ℝ)
    (hadd : ∀ x y : α, x ⊓ y = ⊥ →
      mass (x ⊔ y) = mass x + mass y)
    (hunit : mass ⊤ = 1)
    (htrans : ∀ x y : α,
      prebananaProperZeroMark μ x →
      prebananaProperZeroMark μ y →
      ∃ g : G, g • x = y)
    (hinv : ∀ g : G, ∀ x : α, mass (g • x) = mass x)
    (a b c d e : α)
    (ha : prebananaProperZeroMark μ a)
    (hb : prebananaProperZeroMark μ b)
    (hc : prebananaProperZeroMark μ c)
    (hd : prebananaProperZeroMark μ d)
    (he : prebananaProperZeroMark μ e)
    (hab : a ⊓ b = ⊥)
    (habtop : a ⊔ b = ⊤)
    (hcd : c ⊓ d = ⊥)
    (hce : c ⊓ e = ⊥)
    (hde : d ⊓ e = ⊥)
    (hcdetop : (c ⊔ d) ⊔ e = ⊤) :
    False := by
  exact prebanana_no_uniformMass_two_three μ mass hadd hunit
    (prebanana_invariantMass_constant_on_zeroMark_orbit
      μ mass htrans hinv)
    a b c d e ha hb hc hd he hab habtop hcd hce hde hcdetop

/-- The three-atom all-unmarked Boolean algebra has a disjoint
partition into two nonzero proper unmarked pieces. -/
theorem prebanana_threeAtom_unmarked_pair :
    (({0} : Finset (Fin 3)) ∩ {1, 2} = ∅) ∧
    (({0} : Finset (Fin 3)) ∪ {1, 2} = Finset.univ) := by
  decide

/-- The same finite Boolean algebra has a disjoint partition
into three nonzero proper unmarked pieces. -/
theorem prebanana_threeAtom_unmarked_triple :
    (({0} : Finset (Fin 3)) ∩ {1} = ∅) ∧
    (({0} : Finset (Fin 3)) ∩ {2} = ∅) ∧
    (({1} : Finset (Fin 3)) ∩ {2} = ∅) ∧
    ((({0} : Finset (Fin 3)) ∪ {1}) ∪ {2} = Finset.univ) := by
  decide

end SuccessorTree.NonPrecompact
