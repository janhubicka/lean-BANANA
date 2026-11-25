import BANANA.NonPrecompact.BananaLimitTopologicalAmenability
import BANANA.NonPrecompact.BananaLimitMixedTupleOrbits
import BANANA.NonPrecompact.OrbitCover
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# The mixed-tuple orbit criterion for the native BANANA automorphism group

The stabilisers of finite tagged tuples form a neighbourhood basis.
Finite double-coset covers determine which native subgroups are
co-precompact, and finite tuple orbits determine their closure.
-/

namespace SuccessorTree.NonPrecompact

open Filter MulAction Set Topology

instance : MulAction BananaLimitAutomorphism (BananaLimitVector ⊕ BananaLimitVector) where
  smul g := bananaLimitTaggedAct g.val.1 g.val.2
  one_smul x := by cases x <;> rfl
  mul_smul g h x := by cases x <;> rfl

private theorem bananaLimitEvaluation_eq_untagged_smul
    (g : BananaLimitAutomorphism) (a : BananaLimitVector ⊕ BananaLimitVector) :
    bananaLimitEvaluation g a = Sum.elim id id (g • a) := by
  cases a <;> rfl

private theorem isOpen_bananaLimitTaggedEval
    (a b : BananaLimitVector ⊕ BananaLimitVector) :
    IsOpen {g : BananaLimitAutomorphism | g • a = b} := by
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      change IsOpen {g : BananaLimitAutomorphism |
        (Sum.inl (g.val.1 a) : BananaLimitVector ⊕ BananaLimitVector) = Sum.inl b}
      simpa only [Sum.inl.injEq] using isOpen_bananaLimitEvaluation_left a b
    | inr b =>
      change IsOpen {g : BananaLimitAutomorphism | Sum.inl (g.val.1 a) = Sum.inr b}
      simp
  | inr a =>
    cases b with
    | inl b =>
      change IsOpen {g : BananaLimitAutomorphism | Sum.inr (g.val.2 a) = Sum.inl b}
      simp
    | inr b =>
      change IsOpen {g : BananaLimitAutomorphism |
        (Sum.inr (g.val.2 a) : BananaLimitVector ⊕ BananaLimitVector) = Sum.inr b}
      simpa only [Sum.inr.injEq] using isOpen_bananaLimitEvaluation_right a b

/-- Agreement with prescribed values on a mixed-sort tuple is open. -/
theorem isOpen_bananaLimitTaggedTupleEval {n : ℕ} (a b : BananaLimitTaggedTuple n) :
    IsOpen {g : BananaLimitAutomorphism | g • a = b} := by
  rw [show {g : BananaLimitAutomorphism | g • a = b} =
    ⋂ i : Fin n, {g : BananaLimitAutomorphism | g • a i = b i} by
      ext g
      simp only [mem_ofPred_eq, mem_iInter, funext_iff, Pi.smul_apply]]
  exact isOpen_iInter_of_finite fun i => isOpen_bananaLimitTaggedEval (a i) (b i)

local instance : TopologicalSpace BananaLimitVector := ⊥

/-- Every pointwise neighbourhood contains the fibre of evaluation on a
finite mixed-sort tuple. -/
theorem exists_bananaLimitTaggedTupleEval_subset_of_mem_nhds
    (g : BananaLimitAutomorphism) (U : Set BananaLimitAutomorphism)
    (hU : U ∈ 𝓝 g) :
    ∃ (n : ℕ) (a : BananaLimitTaggedTuple n),
      {h : BananaLimitAutomorphism | h • a = g • a} ⊆ U := by
  classical
  change U ∈ @nhds _ (.induced bananaLimitEvaluation inferInstance) g at hU
  rw [nhds_induced, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, W, hW, hWV⟩ := hV
  let e := Fintype.equivFin I
  let a (i : Fin (Fintype.card I)) : BananaLimitVector ⊕ BananaLimitVector := e.symm i
  refine ⟨Fintype.card I, a, fun h hh => hVU (hWV ?_)⟩
  intro i hi
  have hcoord : h • i = g • i := by
    have hpoint := congrFun hh (e ⟨i, hi⟩)
    simpa only [Pi.smul_apply, a, e.symm_apply_apply] using hpoint
  change bananaLimitEvaluation h i ∈ W i
  rw [bananaLimitEvaluation_eq_untagged_smul, hcoord, ← bananaLimitEvaluation_eq_untagged_smul]
  exact mem_of_mem_nhds (hW i)

/-- The native group has the finite double-coset covering property
exactly when each of its mixed-tuple orbits splits into finitely many
orbits of the subgroup. -/
theorem bananaLimit_coprecompact_iff_finset_taggedTupleOrbitRepresentatives
    (H : Subgroup BananaLimitAutomorphism) :
    CoPrecompact BananaLimitAutomorphism H ↔
      ∀ (n : ℕ) (a : BananaLimitTaggedTuple n),
        ∃ R : Finset (orbit BananaLimitAutomorphism a),
          ∀ x : orbit BananaLimitAutomorphism a, ∃ r ∈ R,
            (x : BananaLimitTaggedTuple n) ∈ orbit H (r : BananaLimitTaggedTuple n) := by
  constructor
  · intro hH n a
    apply (exists_finset_doubleCosetCover_iff_orbit_representatives H a).mp
    have hOpen : IsOpen (stabilizer BananaLimitAutomorphism a : Set BananaLimitAutomorphism) :=
      isOpen_bananaLimitTaggedTupleEval a a
    obtain ⟨F, hF⟩ := hH _ (hOpen.mem_nhds (stabilizer _ a).one_mem)
    refine ⟨F, fun g => ?_⟩
    obtain ⟨f, hf, u, hu, h, heq⟩ := hF g
    exact ⟨f, hf, ⟨u, hu⟩, h, heq⟩
  · intro h U hU
    obtain ⟨n, a, hsub⟩ := exists_bananaLimitTaggedTupleEval_subset_of_mem_nhds 1 U hU
    obtain ⟨F, hF⟩ :=
      (exists_finset_doubleCosetCover_iff_orbit_representatives H a).mpr (h n a)
    refine ⟨F, fun g => ?_⟩
    obtain ⟨f, hf, u, k, heq⟩ := hF g
    exact ⟨f, hf, u, hsub ((mem_stabilizer_iff.mp u.property).trans (one_smul _ _).symm),
      k, heq⟩

/-- Naming the finite mixed-tuple orbits of a native subgroup recovers
its topological closure inside the native group. -/
theorem bananaLimit_mem_topologicalClosure_iff_preserves_taggedTupleOrbits
    (H : Subgroup BananaLimitAutomorphism) (g : BananaLimitAutomorphism) :
    g ∈ H.topologicalClosure ↔
      ∀ (n : ℕ) (a : BananaLimitTaggedTuple n), g • a ∈ orbit H a := by
  change g ∈ (H.topologicalClosure : Set BananaLimitAutomorphism) ↔ _
  rw [Subgroup.topologicalClosure_coe, mem_closure_iff_nhds]
  constructor
  · intro hg n a
    have hU := (isOpen_bananaLimitTaggedTupleEval a (g • a)).mem_nhds
      (show g ∈ {h : BananaLimitAutomorphism | h • a = g • a} from rfl)
    obtain ⟨h, hh, hhH⟩ := hg _ hU
    exact ⟨⟨h, hhH⟩, hh⟩
  · intro hg U hU
    obtain ⟨n, a, hsub⟩ := exists_bananaLimitTaggedTupleEval_subset_of_mem_nhds g U hU
    obtain ⟨h, hh⟩ := hg n a
    exact ⟨h, hsub hh, h.property⟩

/-- Oligomorphicity of a native subgroup implies co-precompactness. -/
theorem bananaLimit_coprecompact_of_finite_taggedTupleOrbitRepresentatives
    (H : Subgroup BananaLimitAutomorphism)
    (hH : ∀ n : ℕ, ∃ R : Finset (BananaLimitTaggedTuple n),
      ∀ x : BananaLimitTaggedTuple n, ∃ r ∈ R, x ∈ orbit H r) :
    CoPrecompact BananaLimitAutomorphism H := by
  classical
  apply (bananaLimit_coprecompact_iff_finset_taggedTupleOrbitRepresentatives H).mpr
  intro n a
  obtain ⟨R, hR⟩ := hH n
  refine ⟨R.subtype (· ∈ orbit BananaLimitAutomorphism a), fun x => ?_⟩
  obtain ⟨r, hr, h, hh⟩ := hR x
  have hrFull : r ∈ orbit BananaLimitAutomorphism a := by
    obtain ⟨g, hg⟩ := x.property
    refine ⟨(h : BananaLimitAutomorphism)⁻¹ * g, ?_⟩
    change ((h : BananaLimitAutomorphism)⁻¹ * g) • a = r
    change g • a = (x : BananaLimitTaggedTuple n) at hg
    change (h : BananaLimitAutomorphism) • r = (x : BananaLimitTaggedTuple n) at hh
    rw [mul_smul, hg, ← hh, inv_smul_smul]
  exact ⟨⟨r, hrFull⟩, Finset.mem_subtype.mpr hr, h, hh⟩

/-- A co-precompact subgroup of the native BANANA group is oligomorphic:
the finitely many ambient orbits each split into finitely many subgroup
orbits. -/
theorem bananaLimit_finite_taggedTupleOrbitRepresentatives_of_coprecompact
    (H : Subgroup BananaLimitAutomorphism) (hH : CoPrecompact BananaLimitAutomorphism H)
    (n : ℕ) : ∃ R : Finset (BananaLimitTaggedTuple n),
      ∀ x : BananaLimitTaggedTuple n, ∃ r ∈ R, x ∈ orbit H r := by
  classical
  obtain ⟨R, hR⟩ := bananaLimit_exists_finite_tagged_tuple_orbit_representatives n
  have hsplit := (bananaLimit_coprecompact_iff_finset_taggedTupleOrbitRepresentatives H).mp hH n
  choose F hF using hsplit
  refine ⟨R.biUnion fun r => (F r).image Subtype.val, fun x => ?_⟩
  obtain ⟨r, hr, EL, ER, hpair, hacts⟩ := hR x
  let g : BananaLimitAutomorphism := ⟨(EL, ER), hpair⟩
  have hg : g • x = r := funext hacts
  let y : orbit BananaLimitAutomorphism r := ⟨x, ⟨g⁻¹, by
    change g⁻¹ • r = x
    rw [← hg, inv_smul_smul]⟩⟩
  obtain ⟨z, hz, hzx⟩ := hF r y
  exact ⟨z.val, Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩, hzx⟩

end SuccessorTree.NonPrecompact
