import Mathlib.Data.Finset.Image
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Finite double-coset covers and orbit representatives

For a group acting on a set, the double cosets of a point stabiliser
and a subgroup correspond, by inversion, to subgroup orbits within
the orbit of the point.
-/

namespace SuccessorTree.NonPrecompact

open MulAction

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

end SuccessorTree.NonPrecompact
