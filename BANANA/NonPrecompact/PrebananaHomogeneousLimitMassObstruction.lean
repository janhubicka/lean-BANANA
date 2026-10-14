import BANANA.NonPrecompact.PrebananaOneGeneratorMarkedIso
import BANANA.NonPrecompact.PrebananaStoneMeasureMass

/-!
# Non-amenability obstruction from marked ultrahomogeneity

This module assembles three verified finite and structural ingredients
of the circulated pre-BANANA non-amenability proof:

1. Proper nonzero zero-marked Boolean elements generate isomorphic
   finite marked Boolean subalgebras, even in an infinite ambient algebra.
2. Ultrahomogeneity of the marked Boolean structure extends such
   finite generated isomorphisms to automorphisms, giving one orbit.
3. An invariant probability measure on a measurable Boolean
   presentation induces a finitely additive mass, contradicting the
   partitions supplied by one embedded unmarked three-atom algebra.

The resulting theorem is conditional **only on explicit interfaces**:
the marked-structure ultrahomogeneity hypothesis, a measurable Boolean
presentation with invariant masses, and an embedded unmarked
three-atom subalgebra. These conditions hold for the intended
pre-BANANA Fraïssé limit by standard facts, but the countable
Fraïssé limit and its Stone space are not constructed here.

No frozen manuscript prose is modified.
-/

namespace SuccessorTree.NonPrecompact

/-- The probability-mass contradiction follows from finite generated
marked ultrahomogeneity and one embedded unmarked three-atom algebra.

The acting group need not be explicitly identified as the full
automorphism group; it is enough that every marked generated finite
isomorphism extends to an element of this group and that the mass is
group invariant. -/
theorem prebanana_no_invariantPresentedProbability_of_ultrahomogeneity
    {β Ω G : Type*}
    [BooleanAlgebra β] [MeasurableSpace Ω]
    [Group G] [MulAction G β]
    (μ : β → F2)
    (hzero : μ ⊥ = 0) (htop : μ ⊤ = 0)
    (hadd : ∀ x y : β, x ⊓ y = ⊥ →
      μ (x ⊔ y) = μ x + μ y)
    (hhomogeneous :
      ∀ (n : ℕ) (xs ys : Fin n → β),
        PrebananaAbstractGeneratedMarkedIso β β xs ys μ μ →
        ∃ g : G, ∀ i : Fin n, g • xs i = ys i)
    (ν : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure ν]
    (ι : BoundedLatticeHom β (Set Ω))
    (hmeas : ∀ x : β, MeasurableSet (ι x))
    (hinvariant : ∀ g : G, ∀ x : β,
      ν.real (ι (g • x)) = ν.real (ι x))
    (f : BoundedLatticeHom (Finset (Fin 3)) β)
    (hinj : Function.Injective f)
    (hmark : ∀ s : Finset (Fin 3), μ (f s) = 0) :
    False := by
  have htrans :
      ∀ x y : β,
        prebananaProperZeroMark μ x →
        prebananaProperZeroMark μ y →
        ∃ g : G, g • x = y := by
    intro x y hx hy
    exact prebananaProperZeroMark_orbit_of_ultrahomogeneity
      μ hzero htop hadd hhomogeneous x y hx hy
  exact prebanana_no_invariantPresentedProbability_of_threeAtom
    (β := β) (Ω := Ω) (G := G)
    μ ν ι hmeas htrans hinvariant f hinj hmark

end SuccessorTree.NonPrecompact
