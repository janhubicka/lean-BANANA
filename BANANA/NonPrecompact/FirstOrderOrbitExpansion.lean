import BANANA.NonPrecompact.FirstOrderOrbitCoPrecompact
import BANANA.NonPrecompact.FirstOrderOligomorphicCategoricity
import Mathlib.Data.Set.Countable
import Mathlib.ModelTheory.LanguageMap

/-!
# Canonical first-order expansions by finite tuple orbits

Naming the tuple orbits of a subgroup in the pointwise topology gives a
first-order expansion whose automorphism group is the subgroup's closure.
-/

namespace SuccessorTree.NonPrecompact.FirstOrderAut

open FirstOrder Set MulAction
open scoped FirstOrder

variable {L : Language} {M : Type*} [L.Structure M]

/-- There is one relation symbol for each orbit on tuples of its arity. -/
def tupleOrbitLanguage (H : Subgroup (FirstOrderAut L M)) : Language where
  Functions _ := Empty
  Relations n := Set.range (orbit H : (Fin n → M) → Set (Fin n → M))

instance tupleOrbitStructure (H : Subgroup (FirstOrderAut L M)) :
    (tupleOrbitLanguage H).Structure M where
  funMap f := Empty.elim f
  RelMap r x := x ∈ r.val

variable (H : Subgroup (FirstOrderAut L M))

/-- Forget the added orbit relations. -/
def restrictOrbitExpansionAut
    (g : FirstOrderAut (L.sum (tupleOrbitLanguage H)) M) : FirstOrderAut L M :=
  ofEquiv {
    g.toEquiv.toEquiv with
    map_fun' := fun f x => g.toEquiv.map_fun' (Sum.inl f) x
    map_rel' := fun r x => g.toEquiv.map_rel' (Sum.inl r) x }

theorem restrictOrbitExpansionAut_mem_closure
    (g : FirstOrderAut (L.sum (tupleOrbitLanguage H)) M) :
    restrictOrbitExpansionAut H g ∈ H.topologicalClosure := by
  apply (mem_topologicalClosure_iff_preserves_tupleOrbits H _).2
  intro n a
  let R : (tupleOrbitLanguage H).Relations n := ⟨orbit H a, a, rfl⟩
  exact (g.toEquiv.map_rel' (Sum.inr R) a).2 (mem_orbit_self a)

/-- Every element of the closure acts on the orbit expansion. -/
def liftOrbitExpansionAut (g : H.topologicalClosure) :
    FirstOrderAut (L.sum (tupleOrbitLanguage H)) M :=
  ofEquiv {
    g.val.toEquiv.toEquiv with
    map_fun' := fun f x => by
      cases f with
      | inl f => exact g.val.toEquiv.map_fun' f x
      | inr f => exact Empty.elim f
    map_rel' := fun r x => by
      cases r with
      | inl r => exact g.val.toEquiv.map_rel' r x
      | inr r =>
        obtain ⟨a, ha⟩ := r.property
        change g.val • x ∈ r.val ↔ x ∈ r.val
        rw [← ha]
        have hx := (mem_topologicalClosure_iff_preserves_tupleOrbits H g.val).1 g.property _ x
        have horbit : orbit H (g.val • x) = orbit H x := (orbit_eq_iff).2 hx
        simp only [← orbit_eq_iff, horbit] }

/-- The reduct of the automorphism group of the expansion is exactly the
pointwise closure of the subgroup. -/
theorem range_restrictOrbitExpansionAut :
    Set.range (restrictOrbitExpansionAut H) = (H.topologicalClosure : Set (FirstOrderAut L M)) := by
  ext g
  constructor
  · rintro ⟨f, rfl⟩
    exact restrictOrbitExpansionAut_mem_closure H f
  · intro hg
    refine ⟨liftOrbitExpansionAut H ⟨g, hg⟩, ?_⟩
    change (restrictOrbitExpansionAut H (liftOrbitExpansionAut H ⟨g, hg⟩)).toEquiv = g.toEquiv
    ext x
    rfl

/-- The expansion and the original subgroup have the same finite tuple orbits. -/
theorem orbit_orbitExpansion_eq {n : ℕ} (a : Fin n → M) :
    orbit (FirstOrderAut (L.sum (tupleOrbitLanguage H)) M) a = orbit H a := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact (mem_topologicalClosure_iff_preserves_tupleOrbits H _).mp
      (restrictOrbitExpansionAut_mem_closure H g) n a
  · rintro ⟨g, rfl⟩
    exact ⟨liftOrbitExpansionAut H ⟨g.val, H.le_topologicalClosure g.property⟩, rfl⟩

/-- A finite list of subgroup orbits gives finitely many added relations
at that arity. -/
theorem finite_tupleOrbitLanguage_relations {n : ℕ}
    (R : Finset (Fin n → M)) (hR : ∀ x : Fin n → M, ∃ r ∈ R, x ∈ orbit H r) :
    Finite ((tupleOrbitLanguage H).Relations n) := by
  classical
  change Finite (Set.range (orbit H : (Fin n → M) → Set (Fin n → M)))
  apply Set.Finite.to_subtype
  refine (R.image (orbit H)).finite_toSet.subset ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨r, hr, hx⟩ := hR x
  exact Finset.mem_image.mpr ⟨r, hr, (orbit_eq_iff.mpr hx).symm⟩

/-- On a countable carrier the canonical expansion adds countably many
symbols. -/
theorem countable_tupleOrbitLanguage_symbols [Countable M] :
    Countable (tupleOrbitLanguage H).Symbols := by
  change Countable ((Σ _ : ℕ, Empty) ⊕
    (Σ n : ℕ, Set.range (orbit H : (Fin n → M) → Set (Fin n → M))))
  letI (n : ℕ) : Countable (Set.range (orbit H : (Fin n → M) → Set (Fin n → M))) :=
    Set.countable_range _
  infer_instance

/-- In an oligomorphic first-order automorphism group, a co-precompact
subgroup gives a countably categorical canonical orbit expansion. -/
theorem categorical_orbitExpansion_of_coprecompact
    (hH : CoPrecompact (FirstOrderAut L M) H)
    (hG : ∀ n : ℕ, ∃ R : Finset (Fin n → M), ∀ x : Fin n → M,
      ∃ r ∈ R, ∃ g : FirstOrderAut L M, g • r = x) :
    Cardinal.Categorical Cardinal.aleph0 ((L.sum (tupleOrbitLanguage H)).completeTheory M) := by
  apply categorical_completeTheory_of_finite_tupleOrbitRepresentatives
  intro n
  obtain ⟨R, hR⟩ := exists_finset_tupleOrbitRepresentatives_of_oligomorphic H hH hG n
  refine ⟨R, fun x => ?_⟩
  obtain ⟨r, hr, h⟩ := hR x
  refine ⟨r, hr, ?_⟩
  change x ∈ orbit (FirstOrderAut (L.sum (tupleOrbitLanguage H)) M) r
  rwa [orbit_orbitExpansion_eq H r]

end SuccessorTree.NonPrecompact.FirstOrderAut
