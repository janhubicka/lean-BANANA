import BANANA.NonPrecompact.TopologicalAmenability
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact

/-!
# Amenability descends to open subgroups

A continuous compact action of an open subgroup admits a compact
coinduced action of the full group. Right translations on the coinduced
functions act continuously, because nearby translates lie in the same
right coset. Evaluation at the identity is subgroup-equivariant.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open Set MeasureTheory

variable {G : Type} [Group G] (H : Subgroup G)
variable (X : Type) [MulAction H X]

/-- The coinduced functions satisfying equivariance for left multiplication. -/
def CoinducedFlow := {f : G → X // ∀ (h : H) (g : G), f ((h : G) * g) = h • f g}

instance [TopologicalSpace X] : TopologicalSpace (CoinducedFlow H X) :=
  instTopologicalSpaceSubtype

instance [TopologicalSpace X] [T2Space X] : T2Space (CoinducedFlow H X) :=
  inferInstanceAs (T2Space {f : G → X // ∀ (h : H) (g : G), f ((h : G) * g) = h • f g})

instance : MulAction G (CoinducedFlow H X) where
  smul g f := ⟨fun x => f.val (x * g), fun h x => by
    simpa only [mul_assoc] using f.property h (x * g)⟩
  one_smul f := by
    apply Subtype.ext
    funext x
    change f.val (x * 1) = f.val x
    rw [mul_one]
  mul_smul g k f := by
    apply Subtype.ext
    funext x
    change f.val (x * (g * k)) = f.val ((x * g) * k)
    rw [mul_assoc]

@[simp]
theorem coinducedFlow_smul_apply (g : G) (f : CoinducedFlow H X) (x : G) :
    (g • f).val x = f.val (x * g) := rfl

instance [Nonempty X] : Nonempty (CoinducedFlow H X) := by
  classical
  let x₀ := Classical.choice (inferInstance : Nonempty X)
  let q (g : G) : Quotient (QuotientGroup.rightRel H) := Quotient.mk _ g
  let rep (g : G) : G := (q g).out
  have hm (g : G) : g * (rep g)⁻¹ ∈ H :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact (Quotient.out_eq (q g)))
  let k (g : G) : H := ⟨g * (rep g)⁻¹, hm g⟩
  refine ⟨⟨fun g => k g • x₀, fun h g => ?_⟩⟩
  have hq : q g = q ((h : G) * g) := Quotient.sound
    (QuotientGroup.rightRel_apply.mpr (by simpa only [mul_assoc, mul_inv_cancel, mul_one] using h.property))
  have hr : rep ((h : G) * g) = rep g := congrArg Quotient.out hq.symm
  have hk : k ((h : G) * g) = h * k g := by
    apply Subtype.ext
    change (h : G) * g * (rep ((h : G) * g))⁻¹ = ↑h * (g * (rep g)⁻¹)
    rw [hr, mul_assoc]
  change k ((h : G) * g) • x₀ = h • (k g • x₀)
  rw [hk, mul_smul]

variable [TopologicalSpace G] [TopologicalSpace X] [ContinuousSMul H X]

private theorem isClosed_coinducedFlow [T2Space X] :
    IsClosed {f : G → X | ∀ (h : H) (g : G), f ((h : G) * g) = h • f g} := by
  have heq : {f : G → X | ∀ (h : H) (g : G), f ((h : G) * g) = h • f g} =
      ⋂ (h : H) (g : G), {f : G → X | f ((h : G) * g) = h • f g} := by
    ext f
    simp
  rw [heq]
  exact isClosed_iInter fun h => isClosed_iInter fun g =>
    isClosed_eq (continuous_apply _) (continuous_const.smul (continuous_apply _))

instance [T2Space X] [CompactSpace X] : CompactSpace (CoinducedFlow H X) :=
  isCompact_iff_compactSpace.mp (isClosed_coinducedFlow H X).isCompact

omit [TopologicalSpace G] [ContinuousSMul H X] in
/-- Evaluation at any coordinate is continuous in the product subspace topology. -/
theorem continuous_coinducedEval (g : G) :
    Continuous (fun f : CoinducedFlow H X => f.val g) :=
  (continuous_apply g).comp continuous_subtype_val

/-- The full group acts continuously when the subgroup is open. -/
theorem continuousSMul_coinducedFlow [IsTopologicalGroup G] (hOpen : IsOpen (H : Set G)) :
    ContinuousSMul G (CoinducedFlow H X) where
  continuous_smul := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro x
    rw [continuous_iff_continuousAt]
    intro p
    change ContinuousAt (fun q : G × CoinducedFlow H X => q.2.val (x * q.1)) p
    let m (q : G × CoinducedFlow H X) : G := x * q.1 * (x * p.1)⁻¹
    have hm : Continuous m :=
      (continuous_const.mul continuous_fst).mul continuous_const
    let U := m ⁻¹' (H : Set G)
    have hU : IsOpen U := hOpen.preimage hm
    have hp : p ∈ U := by change x * p.1 * (x * p.1)⁻¹ ∈ H; simp
    let u (q : U) : H := ⟨m q.val, q.property⟩
    have hu : Continuous u := (hm.comp continuous_subtype_val).subtype_mk _
    have hv : Continuous (fun q : U => q.val.2.val (x * p.1)) :=
      (continuous_coinducedEval H X _).comp (continuous_snd.comp continuous_subtype_val)
    have hEq (q : U) : q.val.2.val (x * q.val.1) =
        u q • q.val.2.val (x * p.1) := by
      have h := q.val.2.property (u q) (x * p.1)
      change q.val.2.val (x * q.val.1 * (x * p.1)⁻¹ * (x * p.1)) =
        u q • q.val.2.val (x * p.1) at h
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
    apply (hU.continuousOn_iff).mp _ hp
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (hu.smul hv).congr (fun q => (hEq q).symm)

/-- Amenability of a topological group passes to every open subgroup. -/
theorem isTopologicallyAmenable_openSubgroup [IsTopologicalGroup G]
    (hOpen : IsOpen (H : Set G)) (hAmen : IsTopologicallyAmenable G) :
    IsTopologicallyAmenable H := by
  intro A _ _ _ _ _ _ _ _
  let Y := CoinducedFlow H A
  letI : ContinuousSMul G Y := continuousSMul_coinducedFlow H A hOpen
  letI : MeasurableSpace Y := borel Y
  letI : BorelSpace Y := ⟨rfl⟩
  obtain ⟨ν, hprob, hinv⟩ := hAmen Y
  letI := hprob
  let ev : Y → A := fun f => f.val 1
  have hev : Measurable ev := (continuous_coinducedEval H A 1).measurable
  refine ⟨ν.map ev, inferInstance, ?_⟩
  intro h
  have hhA : Measurable (fun a : A => h • a) :=
    (continuous_const.smul continuous_id).measurable
  have hhY : Measurable (fun y : Y => (h : G) • y) :=
    ((continuous_const (y := (h : G))).smul (continuous_id : Continuous (id : Y → Y))).measurable
  have hcomp : (fun a : A => h • a) ∘ ev = ev ∘ (fun y : Y => (h : G) • y) := by
    funext y
    change h • y.val 1 = y.val (1 * (h : G))
    simpa only [mul_one, one_mul] using (y.property h 1).symm
  rw [Measure.map_map hhA hev, hcomp, ← Measure.map_map hev hhY, hinv (h : G)]

end SuccessorTree.NonPrecompact.BooleanBanana
