import BANANA.NonPrecompact.BinarySubspaceRamseyInterface
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The last-coordinate dichotomy for binary subspaces

Let P be a binary linear subspace of V × F₂, and let Q be its image
under first-coordinate projection. Exactly the alternatives needed for
greedy pivot coding arise:

* if the vertical unit vector does not lie in P, first projection is
  injective on P (the new coordinate is a dependent linear rule);
* if it does lie in P, then P = Q × F₂ (the new coordinate is a pivot).

This algebraic dichotomy is independent of the successor-tree formalisation.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

open Module

/-- Separate the last coordinate of a finite binary vector. The
first component is the prefix, while the second is the final bit. -/
def lastCoordinateLinearEquiv (n : ℕ) :
    (Fin (n + 1) → F2) ≃ₗ[F2] ((Fin n → F2) × F2) where
  toFun := fun x => (Fin.init x, x (Fin.last n))
  invFun := fun p => Fin.snoc p.1 p.2
  left_inv := by
    intro x
    exact Fin.snoc_init_self x
  right_inv := by
    rintro ⟨x, c⟩
    apply Prod.ext
    · simp
    · simp
  map_add' := by
    intro x y
    apply Prod.ext
    · funext i
      rfl
    · rfl
  map_smul' := by
    intro c x
    apply Prod.ext
    · funext i
      rfl
    · rfl

/-- Transport a finite binary subspace to a product of a shorter
coordinate space and its final coordinate, preserving its dimension. -/
noncomputable def fixedSubspaceLastProduct
    {d n : ℕ} (P : FixedSubspace d (n + 1)) :
    {Q : Submodule F2 ((Fin n → F2) × F2) // finrank F2 Q = d} := by
  refine ⟨P.1.map (lastCoordinateLinearEquiv n).toLinearMap, ?_⟩
  rw [LinearEquiv.finrank_map_eq]
  exact P.2

/-- Transporting a subspace under the last-coordinate linear
equivalence preserves and reflects membership. -/
theorem mem_fixedSubspaceLastProduct
    {d n : ℕ} (P : FixedSubspace d (n + 1))
    (z : Fin (n + 1) → F2) :
    z ∈ P.1 ↔
      lastCoordinateLinearEquiv n z ∈ (fixedSubspaceLastProduct P).1 := by
  change z ∈ P.1 ↔
    lastCoordinateLinearEquiv n z ∈
      P.1.map (lastCoordinateLinearEquiv n).toLinearMap
  constructor
  · intro hz
    exact ⟨z, hz, rfl⟩
  · rintro ⟨w, hw, hzw⟩
    have hwz : w = z :=
      (lastCoordinateLinearEquiv n).injective hzw
    rwa [hwz] at hw

variable {V : Type*} [AddCommGroup V] [Module F2 V]

private def firstCoordinate :
    (V × F2) →ₗ[F2] V :=
  LinearMap.fst F2 V F2

/-- If P contains the vertical unit vector, each fibre of the first
projection is full. -/
theorem subspace_eq_product_of_vertical
    (P : Submodule F2 (V × F2))
    (hvertical : ((0 : V), (1 : F2)) ∈ P) :
    P = (P.map firstCoordinate).prod (⊤ : Submodule F2 F2) := by
  apply le_antisymm
  · intro z hz
    change z.1 ∈ P.map firstCoordinate ∧
      z.2 ∈ (⊤ : Submodule F2 F2)
    constructor
    · exact ⟨z, hz, rfl⟩
    · exact Submodule.mem_top
  · intro z hz
    change z.1 ∈ P.map firstCoordinate ∧
      z.2 ∈ (⊤ : Submodule F2 F2) at hz
    rcases hz.1 with ⟨w, hw, hfirst⟩
    have hd : ((0 : V), z.2 - w.2) ∈ P := by
      simpa using P.smul_mem (z.2 - w.2) hvertical
    have hs : w + ((0 : V), z.2 - w.2) ∈ P :=
      P.add_mem hw hd
    have heq : w + ((0 : V), z.2 - w.2) = z := by
      apply Prod.ext
      · change w.1 + (0 : V) = z.1
        simpa only [add_zero] using hfirst
      · change w.2 + (z.2 - w.2) = z.2
        abel
    rw [heq] at hs
    exact hs

/-- If P does not contain the vertical unit vector, restriction of the
first-coordinate projection is injective. -/
theorem firstCoordinate_injective_of_no_vertical
    (P : Submodule F2 (V × F2))
    (hvertical : ((0 : V), (1 : F2)) ∉ P) :
    Function.Injective (firstCoordinate.comp P.subtype) := by
  intro x y hfirst
  have hfirst' : x.1.1 = y.1.1 := hfirst
  apply Subtype.ext
  apply Prod.ext
  · exact hfirst'
  · by_contra hsecond
    let d : F2 := x.1.2 - y.1.2
    have hd : d ≠ 0 := sub_ne_zero.mpr hsecond
    have hdiff : ((0 : V), d) ∈ P := by
      have hsub : x.1 - y.1 ∈ P :=
        P.sub_mem x.property y.property
      have heq : x.1 - y.1 = ((0 : V), d) := by
        apply Prod.ext
        · simp [hfirst']
        · rfl
      rw [heq] at hsub
      exact hsub
    have hscaled : d⁻¹ • ((0 : V), d) ∈ P :=
      P.smul_mem _ hdiff
    have hone : d⁻¹ • ((0 : V), d) =
        ((0 : V), (1 : F2)) := by
      apply Prod.ext
      · simp
      · change d⁻¹ * d = 1
        exact inv_mul_cancel₀ hd
    rw [hone] at hscaled
    exact hvertical hscaled

/-- If projection onto the first coordinates is injective, the last
coordinate on P is a linear function of the first coordinates. Extend this
function to the full prefix space. -/
theorem exists_linear_last_coordinate_of_injective
    (P : Submodule F2 (V × F2))
    (hinj : Function.Injective (firstCoordinate.comp P.subtype)) :
    ∃ e : V →ₗ[F2] F2,
      ∀ z : V × F2,
        z ∈ P ↔
          z.1 ∈ P.map firstCoordinate ∧ z.2 = e z.1 := by
  let Q : Submodule F2 V := P.map firstCoordinate
  let proj : P →ₗ[F2] Q :=
    (firstCoordinate.comp P.subtype).codRestrict Q (by
      intro z
      exact ⟨z.1, z.2, rfl⟩)
  have hproj_inj : Function.Injective proj := by
    intro x y hxy
    apply hinj
    exact congrArg Subtype.val hxy
  have hproj_surj : Function.Surjective proj := by
    intro q
    obtain ⟨z, hz, hq⟩ := q.property
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact hq
  let E : P ≃ₗ[F2] Q :=
    LinearEquiv.ofBijective proj ⟨hproj_inj, hproj_surj⟩
  let g : Q →ₗ[F2] F2 :=
    ((LinearMap.snd F2 V F2).comp P.subtype).comp E.symm.toLinearMap
  obtain ⟨e, he⟩ := LinearMap.exists_extend g
  have heval (q : Q) : e q.1 = g q := by
    exact LinearMap.congr_fun he q
  have hlast (z : V × F2) (hz : z ∈ P) : z.2 = e z.1 := by
    let pz : P := ⟨z, hz⟩
    let qz : Q := E pz
    have hfirst : qz.1 = z.1 := rfl
    have hsecond : g qz = z.2 := by
      change (E.symm qz).1.2 = z.2
      simpa only [E.symm_apply_apply]
    calc
      z.2 = g qz := hsecond.symm
      _ = e qz.1 := (heval qz).symm
      _ = e z.1 := by rw [hfirst]
  refine ⟨e, ?_⟩
  intro z
  constructor
  · intro hz
    refine ⟨?_, hlast z hz⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨hq, heq⟩
    obtain ⟨w, hw, hfirst⟩ := hq
    have hwlast : w.2 = e w.1 := hlast w hw
    have hzw : z = w := by
      apply Prod.ext
      · exact hfirst.symm
      · calc
          z.2 = e z.1 := heq
          _ = e w.1 := by
            change w.1 = z.1 at hfirst
            exact congrArg e hfirst.symm
          _ = w.2 := hwlast.symm
    exact hzw.symm ▸ hw

/-- The algebraic pivot-or-boring dichotomy. -/
theorem firstCoordinate_injective_or_full_fibres
    (P : Submodule F2 (V × F2)) :
    Function.Injective (firstCoordinate.comp P.subtype) ∨
      P = (P.map firstCoordinate).prod (⊤ : Submodule F2 F2) := by
  by_cases hvertical : ((0 : V), (1 : F2)) ∈ P
  · exact Or.inr (subspace_eq_product_of_vertical P hvertical)
  · exact Or.inl (firstCoordinate_injective_of_no_vertical P hvertical)

/-- The exact dependent-coordinate versus new-pivot alternative used
at the next stage of greedy finite-subspace coding. -/
theorem lastCoordinate_boring_or_pivot
    (P : Submodule F2 (V × F2)) :
    (∃ e : V →ₗ[F2] F2,
      ∀ z : V × F2,
        z ∈ P ↔
          z.1 ∈ P.map firstCoordinate ∧ z.2 = e z.1) ∨
      P = (P.map firstCoordinate).prod (⊤ : Submodule F2 F2) := by
  rcases firstCoordinate_injective_or_full_fibres P with hinj | hpivot
  · exact Or.inl (exists_linear_last_coordinate_of_injective P hinj)
  · exact Or.inr hpivot

/-- When the last coordinate is dependent, projection preserves
dimension. -/
theorem finrank_projected_of_boring
    [FiniteDimensional F2 V]
    (P : Submodule F2 (V × F2))
    (hvertical : ((0 : V), (1 : F2)) ∉ P) :
    finrank F2 (P.map firstCoordinate) = finrank F2 P := by
  let f : P →ₗ[F2] V := firstCoordinate.comp P.subtype
  have hf : Function.Injective f :=
    firstCoordinate_injective_of_no_vertical P hvertical
  change finrank F2 (LinearMap.range f) = finrank F2 P
  exact LinearMap.finrank_range_of_inj hf

/-- When the last coordinate is independent, the dimension drops by
exactly one under projection. -/
theorem finrank_projected_of_pivot
    [FiniteDimensional F2 V]
    (P : Submodule F2 (V × F2))
    (hvertical : ((0 : V), (1 : F2)) ∈ P) :
    finrank F2 P = finrank F2 (P.map firstCoordinate) + 1 := by
  have hp := subspace_eq_product_of_vertical P hvertical
  calc
    finrank F2 P =
        finrank F2
          ((P.map firstCoordinate).prod (⊤ : Submodule F2 F2)) := by
          rw [hp]
    _ = finrank F2
          ((P.map firstCoordinate) × (⊤ : Submodule F2 F2)) :=
        LinearEquiv.finrank_eq
          ((P.map firstCoordinate).prodEquiv (⊤ : Submodule F2 F2))
    _ = finrank F2 (P.map firstCoordinate) + 1 := by
      simp [Module.finrank_prod]

/-- The first-coordinate projection of the last-coordinate product
form of a finite binary subspace. -/
noncomputable def projectedSubspace
    {d n : ℕ} (P : FixedSubspace d (n + 1)) :
    Submodule F2 (Fin n → F2) :=
  (fixedSubspaceLastProduct P).1.map firstCoordinate

/-- In the dependent-coordinate case, projection has the same finite
dimension. -/
theorem projectedSubspace_finrank_boring
    {d n : ℕ} (P : FixedSubspace d (n + 1))
    (hvertical : ((0 : Fin n → F2), (1 : F2)) ∉
      (fixedSubspaceLastProduct P).1) :
    finrank F2 (projectedSubspace P) = d := by
  change finrank F2 ((fixedSubspaceLastProduct P).1.map firstCoordinate) = d
  exact (finrank_projected_of_boring
    (fixedSubspaceLastProduct P).1 hvertical).trans
    (fixedSubspaceLastProduct P).2

/-- In the free-pivot case, projection has dimension one less. -/
theorem projectedSubspace_finrank_pivot
    {d n : ℕ} (P : FixedSubspace (d + 1) (n + 1))
    (hvertical : ((0 : Fin n → F2), (1 : F2)) ∈
      (fixedSubspaceLastProduct P).1) :
    finrank F2 (projectedSubspace P) = d := by
  have hdim :=
    finrank_projected_of_pivot
      (fixedSubspaceLastProduct P).1 hvertical
  have hP := (fixedSubspaceLastProduct P).2
  change
    finrank F2 (fixedSubspaceLastProduct P).1 =
      finrank F2 (projectedSubspace P) + 1 at hdim
  omega

end BinaryWord
end SuccessorTree.NonPrecompact
