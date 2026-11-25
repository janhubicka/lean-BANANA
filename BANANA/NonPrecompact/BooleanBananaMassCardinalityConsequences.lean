import BANANA.NonPrecompact.BooleanBananaMassCardinality
import BANANA.NonPrecompact.BooleanInvariantMass
import BANANA.NonPrecompact.FirstOrderExtremelyAmenableDegree

/-!
# Further consequences for positive-mass subgroups

The finite weighted age supplies a clopen of measure one half and an
infinite sequence of proper zero-marked elements with distinct masses.
These witness failure of extreme amenability and co-precompactness,
respectively.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open MulAction

variable {B : Type} [BooleanAlgebra B]
    {S : Set ℕ} {mark : B → ZMod 2} {ρ : B → ℚ}

variable
  (hAge : ∀ (A : Type) [BooleanAlgebra A] [Fintype A]
    (μ : A → ZMod 2) (η : A → ℚ), IsFinitePositiveMass S μ η →
      ∃ f : BoundedLatticeHom A B, Function.Injective f ∧
        (∀ a, mark (f a) = μ a) ∧ (∀ a, ρ (f a) = η a))

include hAge in
/-- A positive-mass subgroup with a uniform cover has no fixed point on
its Stone space, since its weighted age realises a clopen of mass one half. -/
theorem massSubgroup_not_extremelyAmenable_of_age [Nontrivial B]
    (hcover : UniformMassCover mark (fun b => (ρ b : ℝ) / 2)) :
    ¬ CompactFlowFixedPoint.{0, 0} (massSubgroup mark (fun b => (ρ b : ℝ) / 2)) := by
  obtain ⟨b, _, _, hb, _⟩ := exists_positiveMass_element_of_age hAge
    (n := 1) (d := 1) (by decide) (by decide) (positiveMassDenominators S).one_mem
  have hm : (ρ b : ℝ) / 2 = 1 / 2 := by
    rw [hb]
    norm_num
  intro hFixed
  exact massSubgroup_no_stone_fixedPoint hcover b (by rw [hm]; norm_num)
    (by rw [hm]; norm_num) (hFixed (BooleanSpectrum.Space B))

include hAge in
/-- If the marked group is transitive on its proper nonzero unmarked
elements, an allowed odd prime gives infinitely many mass-subgroup orbits
inside one marked orbit, so the mass subgroup is not co-precompact. -/
theorem massSubgroup_not_coprecompact_of_age
    (hTrans : ∀ a b : B, prebananaProperZeroMark mark a → prebananaProperZeroMark mark b →
      ∃ g : markedAutomorphisms mark, g • a = b)
    {p : ℕ} (hpS : p ∈ S) (hp : p.Prime) (ho : Odd p) :
    ¬ CoPrecompact (markedAutomorphisms mark) (massSubgroup mark (fun b => (ρ b : ℝ) / 2)) := by
  obtain ⟨x, hx, hinj⟩ := exists_even_marked_mass_sequence_of_age hAge hpS hp ho
  let y (k : ℕ) : orbit (markedAutomorphisms mark) (x 0) :=
    ⟨x k, mem_orbit_iff.mpr (hTrans (x 0) (x k) (hx 0) (hx k))⟩
  exact massSubgroup_not_coprecompact (x 0) y hinj

end SuccessorTree.NonPrecompact.BooleanBanana
