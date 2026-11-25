import BANANA.NonPrecompact.FirstOrderPointwiseAutomorphism
import BANANA.NonPrecompact.OrbitCover
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Co-precompact subgroups of pointwise first-order automorphism groups

The finite `UFH` covering property is equivalent to having finitely
many subgroup orbits on every full-group orbit of finite tuples.
The subgroup's topological closure is also exactly the group of
language automorphisms preserving all of its finite-tuple orbits.
-/

namespace SuccessorTree.NonPrecompact.FirstOrderAut

open FirstOrder Set Filter Topology MulAction
open scoped FirstOrder

variable {L : Language} {M : Type*} [L.Structure M]

/-- A finite tuple stabiliser is open. -/
theorem isOpen_tupleStabilizer {n : ℕ} (a : Fin n → M) :
    IsOpen (stabilizer (FirstOrderAut L M) a : Set (FirstOrderAut L M)) := by
  convert isOpen_tupleEval (L := L) a a using 1
  ext g
  change g • a = a ↔ _
  exact ⟨fun h i => congrFun h i, fun h => funext h⟩

/-- Each identity neighbourhood in the pointwise topology contains the
stabiliser of a finite tuple. -/
theorem exists_tupleStabilizer_subset_of_mem_nhds
    (U : Set (FirstOrderAut L M)) (hU : U ∈ 𝓝 (1 : FirstOrderAut L M)) :
    ∃ n : ℕ, ∃ a : Fin n → M,
      (stabilizer (FirstOrderAut L M) a : Set (FirstOrderAut L M)) ⊆ U := by
  obtain ⟨n, a, ha⟩ := exists_tupleEval_subset_of_mem_nhds 1 U hU
  refine ⟨n, a, fun g hg => ha ?_⟩
  change ∀ i, g.toEquiv (a i) = (1 : FirstOrderAut L M).toEquiv (a i)
  exact fun i => congrFun (mem_stabilizer_iff.mp hg) i

/-- The pointwise co-precompactness criterion: every full-group
finite-tuple orbit splits into finitely many subgroup orbits. -/
theorem coprecompact_iff_finset_tupleOrbitRepresentatives
    (H : Subgroup (FirstOrderAut L M)) :
    CoPrecompact (FirstOrderAut L M) H ↔
      ∀ (n : ℕ) (a : Fin n → M),
        ∃ R : Finset (orbit (FirstOrderAut L M) a),
          ∀ x : orbit (FirstOrderAut L M) a, ∃ r ∈ R,
            (x : Fin n → M) ∈ orbit H (r : Fin n → M) := by
  constructor
  · intro hH n a
    apply (exists_finset_doubleCosetCover_iff_orbit_representatives H a).mp
    obtain ⟨F, hF⟩ := hH (stabilizer (FirstOrderAut L M) a)
      ((isOpen_tupleStabilizer (L := L) a).mem_nhds (stabilizer _ a).one_mem)
    refine ⟨F, fun g => ?_⟩
    obtain ⟨f, hf, u, hu, h, heq⟩ := hF g
    exact ⟨f, hf, ⟨u, hu⟩, h, heq⟩
  · intro h U hU
    obtain ⟨n, a, ha⟩ := exists_tupleStabilizer_subset_of_mem_nhds U hU
    obtain ⟨F, hF⟩ := (exists_finset_doubleCosetCover_iff_orbit_representatives H a).mpr (h n a)
    refine ⟨F, fun g => ?_⟩
    obtain ⟨f, hf, u, k, heq⟩ := hF g
    exact ⟨f, hf, u, ha u.property, k, heq⟩

/-- Preserving all finite-tuple orbits is exactly membership in the
subgroup's topological closure. This is the subgroup recovered by naming
those orbits in a canonical expansion. -/
theorem mem_topologicalClosure_iff_preserves_tupleOrbits
    (H : Subgroup (FirstOrderAut L M)) (g : FirstOrderAut L M) :
    g ∈ H.topologicalClosure ↔
      ∀ (n : ℕ) (a : Fin n → M), g • a ∈ orbit H a := by
  change g ∈ (H.topologicalClosure : Set (FirstOrderAut L M)) ↔ _
  rw [Subgroup.topologicalClosure_coe, mem_closure_iff_nhds]
  constructor
  · intro hg n a
    let U : Set (FirstOrderAut L M) := {h | ∀ i, h.toEquiv (a i) = g.toEquiv (a i)}
    have hU : U ∈ 𝓝 g := (isOpen_tupleEval a (g • a)).mem_nhds (fun _ => rfl)
    obtain ⟨h, hhU, hhH⟩ := hg U hU
    exact ⟨⟨h, hhH⟩, funext hhU⟩
  · intro hg U hU
    obtain ⟨n, a, ha⟩ := exists_tupleEval_subset_of_mem_nhds g U hU
    obtain ⟨h, hh⟩ := hg n a
    exact ⟨h, ha (fun i => congrFun hh i), h.property⟩

/-- Passing to the topological closure changes no finite-tuple orbit. -/
theorem topologicalClosure_tupleOrbit_eq
    (H : Subgroup (FirstOrderAut L M)) {n : ℕ} (a : Fin n → M) :
    orbit H.topologicalClosure a = orbit H a := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact (mem_topologicalClosure_iff_preserves_tupleOrbits H (g : FirstOrderAut L M)).mp
      g.property n a
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g, H.le_topologicalClosure g.property⟩, rfl⟩

/-- In an oligomorphic automorphism group a co-precompact subgroup is
itself oligomorphic. Here oligomorphicity is expressed by finite
tuple-orbit representative sets at every arity. -/
theorem exists_finset_tupleOrbitRepresentatives_of_oligomorphic
    (H : Subgroup (FirstOrderAut L M)) (hH : CoPrecompact (FirstOrderAut L M) H)
    (hG : ∀ n : ℕ, ∃ R : Finset (Fin n → M), ∀ x : Fin n → M,
      ∃ r ∈ R, ∃ g : FirstOrderAut L M, g • r = x) :
    ∀ n : ℕ, ∃ R : Finset (Fin n → M), ∀ x : Fin n → M,
      ∃ r ∈ R, ∃ h : H, h • r = x := by
  classical
  intro n
  obtain ⟨R, hR⟩ := hG n
  have hsplit := (coprecompact_iff_finset_tupleOrbitRepresentatives H).mp hH n
  choose T hT using hsplit
  let S := R.biUnion fun r => (T r).image Subtype.val
  refine ⟨S, fun x => ?_⟩
  obtain ⟨r, hr, g, hg⟩ := hR x
  let y : orbit (FirstOrderAut L M) r := ⟨x, ⟨g, hg⟩⟩
  obtain ⟨z, hz, h, hh⟩ := hT r y
  exact ⟨z.val, Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩, h, hh⟩

end SuccessorTree.NonPrecompact.FirstOrderAut
