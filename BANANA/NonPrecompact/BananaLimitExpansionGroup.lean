import BANANA.NonPrecompact.BananaLimitFirstOrderAutomorphism
import BANANA.NonPrecompact.BananaLimitExtremelyAmenableDegree
import BANANA.NonPrecompact.FirstOrderOmittingTypes

/-!
# Automorphism groups of expansions of the tagged BANANA limit

Forgetting added structure preserves point evaluations. The image of an
oligomorphic expansion group is co-precompact in the native group, so
extreme amenability of that expansion group would contradict the native
copy-degree obstruction.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder Set Filter Topology
open scoped FirstOrder

namespace FirstOrderAut

variable {L L' : Language} {M : Type*} [L.Structure M] [L'.Structure M]

/-- Restriction from a language expansion to its reduct. -/
def reductHom (φ : L →ᴸ L') [φ.IsExpansionOn M] :
    FirstOrderAut L' M →* FirstOrderAut L M where
  toFun g := ofEquiv {
    g.toEquiv.toEquiv with
    map_fun' := by
      intro n f x
      simpa only [φ.map_onFunction] using g.toEquiv.map_fun' (φ.onFunction f) x
    map_rel' := by
      intro n r x
      simpa only [φ.map_onRelation] using g.toEquiv.map_rel' (φ.onRelation r) x }
  map_one' := by rfl
  map_mul' g h := by
    apply Language.Equiv.ext
    intro x
    rfl

@[simp]
theorem reductHom_apply (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (g : FirstOrderAut L' M) (x : M) :
    (reductHom φ g).toEquiv x = g.toEquiv x :=
  rfl

/-- Restriction preserves all point evaluations and is continuous for the
pointwise topologies. -/
theorem continuous_reductHom (φ : L →ᴸ L') [φ.IsExpansionOn M] :
    Continuous (reductHom φ : FirstOrderAut L' M → FirstOrderAut L M) := by
  rw [continuous_iff_continuousAt]
  intro g
  rw [continuousAt_def]
  intro U hU
  obtain ⟨n, a, ha⟩ := exists_tupleEval_subset_of_mem_nhds (reductHom φ g) U hU
  exact mem_of_superset ((isOpen_tupleEval a (fun i => g.toEquiv (a i))).mem_nhds
    (fun _ => rfl)) fun h hh => ha hh

end FirstOrderAut

/-- An oligomorphic expansion of the tagged BANANA limit cannot have an
extremely amenable automorphism group. -/
theorem bananaLimit_expansion_not_extremelyAmenable_of_finite_tupleOrbitRepresentatives
    {L : Language} [L.Structure BananaTaggedCarrier]
    (φ : bananaTaggedLanguage →ᴸ L) [φ.IsExpansionOn BananaTaggedCarrier]
    (hL : ∀ n : ℕ, ∃ R : Finset (Fin n → BananaTaggedCarrier),
      ∀ x : Fin n → BananaTaggedCarrier,
        ∃ r ∈ R, ∃ g : FirstOrderAut L BananaTaggedCarrier, g • r = x) :
    ¬ CompactFlowFixedPoint.{0, 0} (FirstOrderAut L BananaTaggedCarrier) := by
  intro hfixed
  let e := bananaLimit_firstOrderAutIso
  let drop := FirstOrderAut.reductHom (M := BananaTaggedCarrier) φ
  let toNative := e.symm.toMulEquiv.toMonoidHom.comp drop
  let H := toNative.range
  have htoNative : Continuous toNative :=
    (map_continuous e.symm).comp (FirstOrderAut.continuous_reductHom φ)
  have hH : CompactFlowFixedPoint.{0, 0} H :=
    CompactFlowFixedPoint.of_denseRange toNative.rangeRestrict
      (htoNative.subtype_mk _) toNative.rangeRestrict_surjective.denseRange hfixed
  apply bananaLimit_not_extremelyAmenable_of_finite_taggedTupleOrbitRepresentatives H _ hH
  intro n
  obtain ⟨R, hR⟩ := hL n
  refine ⟨R, fun x => ?_⟩
  obtain ⟨r, hr, g, hg⟩ := hR x
  refine ⟨r, hr, toNative.rangeRestrict g, funext fun i => ?_⟩
  change (toNative g) • r i = x i
  rw [← bananaLimit_firstOrderAutIso_apply]
  change (e (e.symm (drop g))).toEquiv (r i) = x i
  rw [e.apply_symm_apply]
  rw [show (drop g).toEquiv (r i) = g.toEquiv (r i) from rfl]
  have hi := congrFun hg i
  change g.toEquiv (r i) = x i at hi
  exact hi

/-- No countably categorical expansion of the tagged BANANA limit in a
countable language has an extremely amenable automorphism group. -/
theorem bananaLimit_expansion_not_extremelyAmenable_of_countablyCategorical
    {L : Language.{0, 0}} [L.Structure BananaTaggedCarrier] [Countable L.Symbols]
    (φ : bananaTaggedLanguage →ᴸ L) [φ.IsExpansionOn BananaTaggedCarrier]
    (hCat : (Cardinal.aleph0 : Cardinal.{0}).Categorical (L.completeTheory BananaTaggedCarrier)) :
    ¬ CompactFlowFixedPoint.{0, 0} (FirstOrderAut L BananaTaggedCarrier) := by
  letI : Infinite BananaTaggedCarrier :=
    Cardinal.infinite_iff.mpr (le_of_eq bananaTaggedCarrier_card.symm)
  exact bananaLimit_expansion_not_extremelyAmenable_of_finite_tupleOrbitRepresentatives φ
    (finite_tupleOrbitRepresentatives_of_categorical_completeTheory hCat)

end SuccessorTree.NonPrecompact
