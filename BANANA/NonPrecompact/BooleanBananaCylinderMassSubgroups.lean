import BANANA.NonPrecompact.BooleanBananaMassCardinalityOnMarkedLimit
import BANANA.NonPrecompact.BooleanBananaMarkedOrbit
import BANANA.NonPrecompact.PrebananaFiveAryCylinderUltrahomogeneity

/-!
# Positive-mass expansions on the fixed Boolean–BANANA limit

Every allowed set of odd primes determines a concrete uniform tower.
The marked reduct is identified with the original cylinder limit.
Putting all normalised mass functions on that same marked algebra
gives the continuum of conjugacy classes in its actual pointwise group.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open Cardinal
open scoped Cardinal Pointwise

/-- For every nonempty set of odd primes, the positive-mass tower
can be realised on the fixed Boolean–BANANA limit. -/
theorem nonempty_cylinderPositiveMassRealisation (S : AllowedOddPrimeSet) :
    Nonempty (PositiveMassRealisation prebananaCylinderCountableModel S.val) := by
  obtain ⟨p, hpS⟩ := S.property.1
  obtain ⟨hp, hodd⟩ := S.property.2 p hpS
  exact nonempty_positiveMassRealisation
    prebananaCylinder_hasFiniteAmbients_forHomogeneity
    prebananaCylinder_hasFiniteExtensionProperty_forHomogeneity hpS hp hodd

/-- The Boolean–BANANA automorphism group has exactly continuum many
conjugacy classes of closed maximal amenable subgroups. -/
theorem mk_cylinderClosedMaximalAmenableConjugacyClass :
    #(ClosedMaximalAmenableConjugacyClass
      (markedAutomorphisms prebananaFiveAryCylinderMark)) = 𝔠 :=
  mk_closedMaximalAmenableConjugacyClass_of_markedLimit
    prebananaCylinder_hasFiniteAmbients_forHomogeneity
    prebananaCylinder_hasFiniteExtensionProperty_forHomogeneity

/-- The actual positive-mass subgroup is closed and maximal amenable,
is not extremely amenable, and is not co-precompact in the original
pointwise marked automorphism group. -/
theorem cylinderMassSubgroup_properties {S : AllowedOddPrimeSet}
    (R : PositiveMassRealisation prebananaCylinderCountableModel S.val) :
    let G := markedAutomorphisms prebananaFiveAryCylinderMark
    let H := massSubgroup prebananaFiveAryCylinderMark R.normalizedMass
    IsClosed (H : Set G) ∧ IsTopologicallyAmenable H ∧
      (∀ J : Subgroup G, H ≤ J → IsTopologicallyAmenable J → J = H) ∧
      ¬ CompactFlowFixedPoint.{0, 0} H ∧ ¬ CoPrecompact G H := by
  obtain ⟨p, hpS⟩ := S.property.1
  obtain ⟨hp, hodd⟩ := S.property.2 p hpS
  refine ⟨isClosed_massSubgroup _ _, R.massSubgroup_amenable,
    fun J hJ hAmen => massSubgroup_eq_of_amenable_supergroup R.uniformTower.uniformMassCover
      J hJ hAmen, R.not_extremelyAmenable, R.not_coprecompact ?_ hpS hp hodd⟩
  intro a b ha hb
  exact properZeroMark_transitive_of_finiteExtension
    prebananaCylinder_hasFiniteAmbients_forHomogeneity
    prebananaCylinder_hasFiniteExtensionProperty_forHomogeneity
    ha.1 ha.2.1 ha.2.2 hb.1 hb.2.1 hb.2.2

/-- Different prime sets give nonconjugate positive-mass subgroups
inside the same Boolean–BANANA group. -/
theorem cylinderMassSubgroups_not_conjugate {S T : AllowedOddPrimeSet} (hne : S ≠ T)
    (R : PositiveMassRealisation prebananaCylinderCountableModel S.val)
    (Q : PositiveMassRealisation prebananaCylinderCountableModel T.val) :
    ¬ ∃ g : ConjAct (markedAutomorphisms prebananaFiveAryCylinderMark),
      g • massSubgroup prebananaFiveAryCylinderMark R.normalizedMass =
        massSubgroup prebananaFiveAryCylinderMark Q.normalizedMass :=
  positiveMassRealisations_not_conjugate hne R Q

end SuccessorTree.NonPrecompact.BooleanBanana
