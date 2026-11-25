import BANANA.NonPrecompact.UniversalMinimalFlow
import Mathlib.Topology.Algebra.Semigroup

/-!
# Coalescence and uniqueness of universal minimal flows

The pointwise closure of a group's action maps contains a minimal subflow.
Composition on the right by any member preserves this subflow. An Ellis
idempotent then makes every equivariant endomorphism a right translation
with a surjective right inverse. The universal property transfers this
coalescence to the original flow.
-/

namespace SuccessorTree.NonPrecompact

open Function MulAction Set Topology
open scoped Pointwise

universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G]

omit [TopologicalSpace G] in
private theorem surjective_of_compact_equivariant
    {X : Type v} {Y : Type w} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [MulAction G X] [MulAction G Y] [IsMinimal G Y]
    (f : X → Y) (hf : Continuous f) (heq : ∀ g : G, ∀ x, f (g • x) = g • f x) :
    Surjective f := by
  apply range_eq_univ.mp
  apply (eq_empty_or_univ_of_smul_invariant_closed G (isCompact_range hf).isClosed ?_).resolve_left
  · exact (range_nonempty f).ne_empty
  · rintro g _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨g • x, heq g x⟩

private def envelopingSubaction (G : Type u) (X : Type v) [Group G] [TopologicalSpace G]
    [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] : SubMulAction G (X → X) :=
  ⟨closure (orbit G (id : X → X)), fun g p hp =>
    smul_closure_orbit_subset g (id : X → X) ⟨p, hp, rfl⟩⟩

/-- Every continuous equivariant self-map of a universal minimal flow is bijective.
It suffices to have universality among flows in the carrier's universe. -/
theorem universalMinimalFlow_coalescent
    {M : Type v} [TopologicalSpace M] [CompactSpace M] [T2Space M] [Nonempty M]
    [MulAction G M] [ContinuousSMul G M] [IsMinimal G M]
    (hUniversal : UniversalAmongMinimalFlows.{u,v,v} G M)
    (f : M → M) (hf : Continuous f) (hfeq : ∀ g : G, ∀ x, f (g • x) = g • f x) :
    Bijective f := by
  classical
  refine ⟨?_, surjective_of_compact_equivariant (G := G) f hf hfeq⟩
  let E := envelopingSubaction G M
  have : CompactSpace E := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  have : Nonempty E := ⟨⟨id, subset_closure (mem_orbit_self _)⟩⟩
  have : ContinuousSMul G E :=
    ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  obtain ⟨I, hcompact, hnonempty, hcontinuous, hminimal⟩ :=
    exists_compact_minimal_subaction G E
  let _ := hcompact
  let _ := hnonempty
  let _ := hcontinuous
  let _ := hminimal
  let toFun (p : I) : M → M := p.val.val
  have htoFun : IsInducing toFun := IsInducing.subtypeVal.comp IsInducing.subtypeVal
  have htoFunInj : Injective toFun := Subtype.val_injective.comp Subtype.val_injective
  let act (g : G) : E := ⟨g • (id : M → M), subset_closure ⟨g, rfl⟩⟩
  have hact : DenseRange act := by
    rw [DenseRange, IsInducing.subtypeVal.dense_iff, ← range_comp]
    exact fun p => p.property
  -- The right operand belongs to the closed invariant set I. Right
  -- composition sends the action maps into I, hence all of E into I.
  have comp_mem (p : E) (q : I) : p.val ∘ toFun q ∈ range toFun := by
    show p.val ∈ (fun r : M → M => r ∘ toFun q) ⁻¹' range toFun
    apply closure_minimal _ ((isCompact_range htoFun.continuous).isClosed.preimage
      (Pi.continuous_precomp (toFun q))) p.property
    rintro _ ⟨g, rfl⟩
    exact ⟨g • q, rfl⟩
  let comp (p : E) (q : I) : I := Classical.choose (comp_mem p q)
  have hcomp (p : E) (q : I) : toFun (comp p q) = p.val ∘ toFun q :=
    Classical.choose_spec (comp_mem p q)
  have hcompContinuous (q : I) : Continuous (fun p : E => comp p q) := by
    apply htoFun.continuous_iff.mpr
    change Continuous (fun p : E => toFun (comp p q))
    simp only [hcomp]
    exact (Pi.continuous_precomp (toFun q)).comp continuous_subtype_val
  have hcompGroup (g : G) (q : I) : comp (act g) q = g • q := by
    apply htoFunInj
    rw [hcomp]
    rfl
  let _ : Semigroup I :=
    { mul := fun p q => comp p.val q
      mul_assoc := by
        intro p q r
        apply htoFunInj
        change toFun (comp (comp p.val q).val r) = toFun (comp p.val (comp q.val r))
        rw [hcomp, hcomp]
        change toFun (comp p.val q) ∘ toFun r = toFun p ∘ toFun (comp q.val r)
        rw [hcomp, hcomp, Function.comp_assoc] }
  have hrightContinuous (q : I) : Continuous (· * q : I → I) :=
    (hcompContinuous q).comp continuous_subtype_val
  have hright (q : I) : Surjective (· * q : I → I) := by
    apply surjective_of_compact_equivariant (G := G) _ (hrightContinuous q)
    intro g p
    apply htoFunInj
    change toFun (comp (g • p).val q) = toFun (g • comp p.val q)
    change toFun (comp (g • p).val q) = g • toFun (comp p.val q)
    rw [hcomp, hcomp]
    rfl
  obtain ⟨e, he⟩ := exists_idempotent_of_compact_t2_of_continuous_mul_left hrightContinuous
  have hrightId (p : I) : p * e = p := by
    obtain ⟨q, rfl⟩ := hright e p
    rw [mul_assoc, he]
  have hcoalescent (F : I → I) (hF : Continuous F)
      (hFeq : ∀ g : G, ∀ p, F (g • p) = g • F p) : Injective F := by
    have hcomm (q : I) : (fun p : E => F (comp p q)) = fun p => comp p (F q) := by
      apply Continuous.ext_on hact (hF.comp (hcompContinuous q)) (hcompContinuous (F q))
      rintro _ ⟨g, rfl⟩
      change F (comp (act g) q) = comp (act g) (F q)
      rw [hcompGroup, hFeq, hcompGroup]
    have htranslate (p : I) : F p = p * F e := by
      have h := congrFun (hcomm e) p.val
      change F (p * e) = p * F e at h
      rwa [hrightId] at h
    obtain ⟨q, hq⟩ := hright (F e) e
    change q * F e = e at hq
    have hinverse (p : I) : F (p * q) = p := by
      rw [htranslate, mul_assoc, hq, hrightId]
    intro x y hxy
    obtain ⟨p, rfl⟩ := hright q x
    obtain ⟨r, rfl⟩ := hright q y
    exact congrArg (· * q) ((hinverse p).symm.trans (hxy.trans (hinverse r)))
  -- An evaluation factor I → M and the universal factor M → I
  -- test injectivity back in the coalescent minimal subflow.
  let ev (p : I) := toFun p (Classical.choice ‹Nonempty M›)
  have hev : Continuous ev := (continuous_apply _).comp htoFun.continuous
  have heveq (g : G) (p : I) : ev (g • p) = g • ev p := rfl
  have hevsurj := surjective_of_compact_equivariant (G := G) ev hev heveq
  obtain ⟨h, hh, _, hheq⟩ := hUniversal I
  have hinj : Injective (fun p : I => h (f (ev p))) :=
    hcoalescent _ (hh.comp (hf.comp hev)) (fun g p => by
      rw [heveq, hfeq, hheq])
  intro x y hxy
  obtain ⟨p, rfl⟩ := hevsurj x
  obtain ⟨q, rfl⟩ := hevsurj y
  exact congrArg ev (hinj (congrArg h hxy))

/-- Two compact Hausdorff universal minimal flows are equivariantly homeomorphic.
The universe hypotheses specify the three instances of the universal property
used in the proof. In a single carrier universe the first two coincide. -/
theorem universalMinimalFlow_unique
    {M : Type v} {N : Type w} [TopologicalSpace M] [CompactSpace M] [T2Space M] [Nonempty M]
    [MulAction G M] [ContinuousSMul G M] [IsMinimal G M]
    [TopologicalSpace N] [CompactSpace N] [T2Space N] [Nonempty N]
    [MulAction G N] [ContinuousSMul G N] [IsMinimal G N]
    (hMself : UniversalAmongMinimalFlows.{u,v,v} G M)
    (hM : UniversalAmongMinimalFlows.{u,v,w} G M)
    (hN : UniversalAmongMinimalFlows.{u,w,v} G N) :
    ∃ e : M ≃ₜ N, ∀ g : G, ∀ x, e (g • x) = g • e x := by
  obtain ⟨f, hf, hfsurj, hfeq⟩ := hM N
  obtain ⟨r, hr, _, hreq⟩ := hN M
  have hinj : Injective (r ∘ f) :=
    (universalMinimalFlow_coalescent hMself _ (hr.comp hf) (fun g x => by
      change r (f (g • x)) = g • r (f x)
      rw [hfeq, hreq])).injective
  let e : M ≃ N := Equiv.ofBijective f ⟨fun _ _ h => hinj (congrArg r h), hfsurj⟩
  exact ⟨e.toHomeomorphOfContinuousClosed hf hf.isClosedMap, hfeq⟩

end SuccessorTree.NonPrecompact
