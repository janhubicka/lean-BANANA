import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Tactic.Linarith

/-!
# The invariant-mass obstruction on a Boolean algebra

A Boolean algebra with a finite additive probability mass cannot have
all proper nonzero unmarked elements of equal mass if it contains an
unmarked three-atom subalgebra. This common argument supports both
Boolean–BANANA and interval actions in Folkman–BANANA.
-/

namespace SuccessorTree.NonPrecompact

/-- The family of proper, nonzero, unmarked Boolean elements. -/
def prebananaProperZeroMark
    {α : Type*} [BooleanAlgebra α]
    (μ : α → ZMod 2) (x : α) : Prop :=
  x ≠ ⊥ ∧ x ≠ ⊤ ∧ μ x = 0

/-- No finitely additive mass on a Boolean algebra can assign
one common value to every proper nonzero zero-marked element if
the unit admits disjoint partitions into two and three of them. -/
theorem prebanana_no_uniformMass_two_three
    {α : Type*} [BooleanAlgebra α]
    (μ : α → ZMod 2) (mass : α → ℝ)
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
    rw [inf_comm (c ⊔ d) e, inf_sup_left]
    rw [inf_comm e c, inf_comm e d, hce, hde]
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
    (μ : α → ZMod 2) (mass : α → ℝ)
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
    (μ : α → ZMod 2) (mass : α → ℝ)
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

/-- A marked, injective embedding of the unmarked three-atom
powerset supplies the two and three partitions required to
rule out one common finitely additive mass on the proper
nonzero zero-marked elements of the target. -/
theorem prebanana_no_uniformMass_of_threeAtom_copy
    {β : Type*} [BooleanAlgebra β]
    (μ : β → ZMod 2) (mass : β → ℝ)
    (hadd : ∀ x y : β, x ⊓ y = ⊥ →
      mass (x ⊔ y) = mass x + mass y)
    (hunit : mass ⊤ = 1)
    (hequal : ∀ x y : β,
      prebananaProperZeroMark μ x →
      prebananaProperZeroMark μ y →
      mass x = mass y)
    (f : BoundedLatticeHom (Finset (Fin 3)) β)
    (hinj : Function.Injective f)
    (hmark : ∀ s : Finset (Fin 3), μ (f s) = 0) :
    False := by
  let a : Finset (Fin 3) := {0}
  let b : Finset (Fin 3) := {1, 2}
  let d : Finset (Fin 3) := {1}
  let e : Finset (Fin 3) := {2}
  have hproper (s : Finset (Fin 3))
      (hbot : s ≠ ∅) (htop : s ≠ Finset.univ) :
      prebananaProperZeroMark μ (f s) := by
    refine ⟨?_, ?_, hmark s⟩
    · intro h
      apply hbot
      apply hinj
      calc
        f s = ⊥ := h
        _ = f (⊥ : Finset (Fin 3)) := (map_bot f).symm
    · intro h
      apply htop
      apply hinj
      calc
        f s = ⊤ := h
        _ = f (⊤ : Finset (Fin 3)) := (map_top f).symm
  have hdj (s t : Finset (Fin 3))
      (h : s ∩ t = ∅) : f s ⊓ f t = ⊥ := by
    have h' : s ⊓ t = (⊥ : Finset (Fin 3)) := by simpa using h
    calc
      f s ⊓ f t = f (s ⊓ t) := (map_inf f s t).symm
      _ = f ⊥ := congrArg f h'
      _ = ⊥ := map_bot f
  have hjoin (s t : Finset (Fin 3))
      (h : s ∪ t = Finset.univ) : f s ⊔ f t = ⊤ := by
    have h' : s ⊔ t = (⊤ : Finset (Fin 3)) := by simpa using h
    calc
      f s ⊔ f t = f (s ⊔ t) := (map_sup f s t).symm
      _ = f ⊤ := congrArg f h'
      _ = ⊤ := map_top f
  have ha0 : a ≠ ∅ := by decide
  have ha1 : a ≠ Finset.univ := by decide
  have hb0 : b ≠ ∅ := by decide
  have hb1 : b ≠ Finset.univ := by decide
  have hd0 : d ≠ ∅ := by decide
  have hd1 : d ≠ Finset.univ := by decide
  have he0 : e ≠ ∅ := by decide
  have he1 : e ≠ Finset.univ := by decide
  have hpair :
      a ∩ b = ∅ ∧ a ∪ b = Finset.univ := by
    simpa [a, b] using prebanana_threeAtom_unmarked_pair
  have htriple :
      a ∩ d = ∅ ∧ a ∩ e = ∅ ∧ d ∩ e = ∅ ∧
        (a ∪ d) ∪ e = Finset.univ := by
    simpa [a, d, e] using prebanana_threeAtom_unmarked_triple
  rcases hpair with ⟨hpairdj, hpairtop⟩
  rcases htriple with ⟨had, hae, hde, htrtop⟩
  have htripleTop : (f a ⊔ f d) ⊔ f e = ⊤ := by
    have htr' : (a ⊔ d) ⊔ e = (⊤ : Finset (Fin 3)) := by
      simpa using htrtop
    calc
      (f a ⊔ f d) ⊔ f e = f (a ⊔ d) ⊔ f e := by
        rw [map_sup f a d]
      _ = f ((a ⊔ d) ⊔ e) :=
        (map_sup f (a ⊔ d) e).symm
      _ = f ⊤ := congrArg f htr'
      _ = ⊤ := map_top f
  exact prebanana_no_uniformMass_two_three μ mass hadd hunit hequal
    (f a) (f b) (f a) (f d) (f e)
    (hproper a ha0 ha1) (hproper b hb0 hb1)
    (hproper a ha0 ha1) (hproper d hd0 hd1)
    (hproper e he0 he1)
    (hdj a b hpairdj) (hjoin a b hpairtop)
    (hdj a d had) (hdj a e hae) (hdj d e hde)
    htripleTop

/-- A group-invariant mass is impossible once the target contains
one unmarked three-atom copy and the group is transitive on the
proper nonzero zero-marked elements. -/
theorem prebanana_no_invariantMass_of_threeAtom_copy
    {β G : Type*}
    [BooleanAlgebra β] [Group G] [MulAction G β]
    (μ : β → ZMod 2) (mass : β → ℝ)
    (hadd : ∀ x y : β, x ⊓ y = ⊥ →
      mass (x ⊔ y) = mass x + mass y)
    (hunit : mass ⊤ = 1)
    (htrans : ∀ x y : β,
      prebananaProperZeroMark μ x →
      prebananaProperZeroMark μ y →
      ∃ g : G, g • x = y)
    (hinv : ∀ g : G, ∀ x : β, mass (g • x) = mass x)
    (f : BoundedLatticeHom (Finset (Fin 3)) β)
    (hinj : Function.Injective f)
    (hmark : ∀ s : Finset (Fin 3), μ (f s) = 0) :
    False :=
  prebanana_no_uniformMass_of_threeAtom_copy μ mass hadd hunit
    (prebanana_invariantMass_constant_on_zeroMark_orbit
      μ mass htrans hinv)
    f hinj hmark

open MeasureTheory

/-- The probability mass induced by a Boolean representation
whose values are measurable subsets of a probability space. -/
noncomputable def prebananaPresentedProbabilityMass
    {β Ω : Type*}
    [BooleanAlgebra β] [MeasurableSpace Ω]
    (ν : Measure Ω)
    (ι : BoundedLatticeHom β (Set Ω)) : β → ℝ :=
  fun x => ν.real (ι x)

/-- The induced mass is finitely additive on disjoint joins. -/
theorem prebananaPresentedProbabilityMass_additive
    {β Ω : Type*}
    [BooleanAlgebra β] [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ι : BoundedLatticeHom β (Set Ω))
    (hmeas : ∀ x : β, MeasurableSet (ι x))
    (x y : β) (hxy : x ⊓ y = ⊥) :
    prebananaPresentedProbabilityMass ν ι (x ⊔ y) =
      prebananaPresentedProbabilityMass ν ι x +
      prebananaPresentedProbabilityMass ν ι y := by
  have hd : Disjoint (ι x) (ι y) := by
    apply disjoint_iff.mpr
    calc
      ι x ⊓ ι y = ι (x ⊓ y) := (map_inf ι x y).symm
      _ = ι ⊥ := congrArg ι hxy
      _ = ⊥ := map_bot ι
  change ν.real (ι (x ⊔ y)) = ν.real (ι x) + ν.real (ι y)
  rw [map_sup ι x y]
  exact measureReal_union hd (hmeas y)

/-- The induced mass assigns unit mass to the top Boolean element. -/
theorem prebananaPresentedProbabilityMass_top
    {β Ω : Type*}
    [BooleanAlgebra β] [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ι : BoundedLatticeHom β (Set Ω)) :
    prebananaPresentedProbabilityMass ν ι (⊤ : β) = 1 := by
  change ν.real (ι (⊤ : β)) = 1
  rw [map_top ι]
  exact probReal_univ

/-- An invariant probability mass on the measurable presentation
contradicts the unmarked three-atom partitions whenever the action
is transitive on the proper nonzero zero-marked Boolean elements.

For a Stone space, the hypotheses about the presentation are standard:
each Boolean element denotes a clopen (hence measurable) set, and
a group-invariant probability measure has invariant clopen masses.
-/
theorem prebanana_no_invariantPresentedProbability_of_threeAtom
    {β Ω G : Type*}
    [BooleanAlgebra β] [MeasurableSpace Ω]
    [Group G] [MulAction G β]
    (μ : β → ZMod 2)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (ι : BoundedLatticeHom β (Set Ω))
    (hmeas : ∀ x : β, MeasurableSet (ι x))
    (htrans : ∀ x y : β,
      prebananaProperZeroMark μ x →
      prebananaProperZeroMark μ y →
      ∃ g : G, g • x = y)
    (hinvariant : ∀ g : G, ∀ x : β,
      ν.real (ι (g • x)) = ν.real (ι x))
    (f : BoundedLatticeHom (Finset (Fin 3)) β)
    (hinj : Function.Injective f)
    (hmark : ∀ s : Finset (Fin 3), μ (f s) = 0) :
    False := by
  exact prebanana_no_invariantMass_of_threeAtom_copy
    (β := β) (G := G) μ (prebananaPresentedProbabilityMass ν ι)
    (fun x y hxy =>
      prebananaPresentedProbabilityMass_additive ν ι hmeas x y hxy)
    (prebananaPresentedProbabilityMass_top ν ι)
    htrans (fun g x => hinvariant g x) f hinj hmark

end SuccessorTree.NonPrecompact
