import Mathlib.Data.Finset.Image
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Topology.Neighborhoods

/-!
# Finite double-coset covers and orbit representatives

For a group acting on a set, the double cosets of a point stabiliser
and a subgroup correspond, by inversion, to subgroup orbits within
the orbit of the point.
-/

namespace SuccessorTree.NonPrecompact

open MulAction Set Filter Topology

variable {G X : Type*} [Group G] [MulAction G X]

/-- Inverse images of a point lie in the same subgroup orbit exactly
when the corresponding elements lie in the same double coset. -/
theorem inverse_smul_mem_subgroup_orbit_iff (H : Subgroup G) (a : X) (g f : G) :
    g⁻¹ • a ∈ orbit H (f⁻¹ • a) ↔
      ∃ (u : stabilizer G a) (h : H), g = (u : G) * f * (h : G) := by
  constructor
  · rintro ⟨k, hk⟩
    change (k : G) • (f⁻¹ • a) = g⁻¹ • a at hk
    have hu : g * (k : G) * f⁻¹ ∈ stabilizer G a := by
      rw [mem_stabilizer_iff, mul_smul, mul_smul, hk, smul_inv_smul]
    refine ⟨⟨_, hu⟩, k⁻¹, ?_⟩
    change g = g * (k : G) * f⁻¹ * f * (k : G)⁻¹
    simp [mul_assoc]
  · rintro ⟨u, h, rfl⟩
    refine ⟨h⁻¹, ?_⟩
    change (h : G)⁻¹ • (f⁻¹ • a) = ((u : G) * f * (h : G))⁻¹ • a
    have hu : (u : G)⁻¹ • a = a :=
      mem_stabilizer_iff.mp ((stabilizer G a).inv_mem u.property)
    simp [mul_inv_rev, mul_smul, hu]

/-- A finite double-coset cover is equivalent to finitely many
subgroup orbit representatives in the orbit of the point. -/
theorem exists_finset_doubleCosetCover_iff_orbit_representatives
    (H : Subgroup G) (a : X) :
    (∃ F : Finset G, ∀ g : G, ∃ f ∈ F,
      ∃ (u : stabilizer G a) (h : H), g = (u : G) * f * (h : G)) ↔
    (∃ R : Finset (orbit G a), ∀ x : orbit G a, ∃ r ∈ R,
      (x : X) ∈ orbit H (r : X)) := by
  classical
  constructor
  · rintro ⟨F, hF⟩
    let repr (f : G) : orbit G a := ⟨f⁻¹ • a, mem_orbit _ _⟩
    refine ⟨F.image repr, fun x => ?_⟩
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp x.property
    obtain ⟨f, hf, hgf⟩ := hF g⁻¹
    refine ⟨repr f, Finset.mem_image.mpr ⟨f, hf, rfl⟩, ?_⟩
    change (x : X) ∈ orbit H (f⁻¹ • a)
    rw [← hg, ← inv_inv g]
    exact (inverse_smul_mem_subgroup_orbit_iff H a g⁻¹ f).2 hgf
  · rintro ⟨R, hR⟩
    let representative (x : orbit G a) : G :=
      (Classical.choose (mem_orbit_iff.mp x.property))⁻¹
    have hrep (x : orbit G a) : (representative x)⁻¹ • a = (x : X) := by
      simpa only [representative, inv_inv] using Classical.choose_spec (mem_orbit_iff.mp x.property)
    refine ⟨R.image representative, fun g => ?_⟩
    obtain ⟨r, hr, hgr⟩ := hR ⟨g⁻¹ • a, mem_orbit _ _⟩
    refine ⟨representative r, Finset.mem_image.mpr ⟨r, hr, rfl⟩, ?_⟩
    apply (inverse_smul_mem_subgroup_orbit_iff H a g (representative r)).1
    rw [hrep]
    exact hgr

/-- Co-precompactness in the finite `UFH` form of the manuscript. -/
def CoPrecompact (G : Type*) [Group G] [TopologicalSpace G] (H : Subgroup G) : Prop :=
  ∀ U : Set G, U ∈ 𝓝 (1 : G) → ∃ F : Finset G, ∀ g : G,
    ∃ f ∈ F, ∃ u ∈ U, ∃ h : H, g = u * f * (h : G)

/-- The double-coset bound for a transitive discrete action with open
point stabiliser. Here the group topology is arbitrary. -/
theorem exists_finset_orbitRepresentatives_of_coprecompact
    {G X : Type*} [Group G] [TopologicalSpace G] [MulAction G X]
    (H : Subgroup G) (hH : CoPrecompact G H) (a : X)
    (haOpen : IsOpen (stabilizer G a : Set G))
    (htrans : ∀ x : X, ∃ g : G, g • a = x) :
    ∃ R : Finset X, ∀ x : X, ∃ r ∈ R, ∃ h : H, h • r = x := by
  classical
  obtain ⟨F, hF⟩ := hH (stabilizer G a : Set G)
    (haOpen.mem_nhds (stabilizer G a).one_mem)
  let r (f : G) := f⁻¹ • a
  refine ⟨F.image r, fun x => ?_⟩
  obtain ⟨g, hg⟩ := htrans x
  obtain ⟨f, hf, u, hu, h, hcover⟩ := hF g⁻¹
  obtain ⟨k, hk⟩ := (inverse_smul_mem_subgroup_orbit_iff H a g⁻¹ f).mpr
    ⟨⟨u, hu⟩, h, hcover⟩
  exact ⟨r f, Finset.mem_image.mpr ⟨f, hf, rfl⟩, k, by simpa [r, hg] using hk⟩

/-- The finite covering property passes to larger subgroups, in
particular to the topological closure of a subgroup. -/
theorem CoPrecompact.mono {G : Type*} [Group G] [TopologicalSpace G]
    {H K : Subgroup G} (hH : CoPrecompact G H) (hHK : H ≤ K) : CoPrecompact G K := by
  intro U hU
  obtain ⟨F, hF⟩ := hH U hU
  refine ⟨F, fun g => ?_⟩
  obtain ⟨f, hf, u, hu, h, heq⟩ := hF g
  exact ⟨f, hf, u, hu, ⟨h, hHK h.property⟩, heq⟩

end SuccessorTree.NonPrecompact
