import BANANA.NonPrecompact.BooleanBananaMassCardinalityConsequences
import BANANA.NonPrecompact.BooleanBananaPositiveMassOnMarkedLimit

/-!
# Maximal amenable subgroups on the fixed marked limit

Transporting each positive-mass tower to the same marked algebra gives the
closed maximal amenable subgroups on that algebra. All the conjugacy
classes below are taken in the original marked automorphism group.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open scoped Cardinal Pointwise

namespace PositiveMassRealisation

variable {M : PrebananaCountableBooleanModel} {S : Set ℕ}
  (R : PositiveMassRealisation M S)

/-- A positive-mass realisation on the fixed reduct gives a closed maximal
amenable subgroup of that reduct's automorphism group. -/
noncomputable def closedMaximalAmenableSubgroup :
    ClosedMaximalAmenableSubgroup (markedAutomorphisms M.μ) :=
  ⟨massSubgroup M.μ R.normalizedMass, isClosed_massSubgroup M.μ R.normalizedMass,
    R.massSubgroup_amenable, fun J hJ hAmen =>
      massSubgroup_eq_of_amenable_supergroup R.uniformTower.uniformMassCover J hJ hAmen⟩

/-- The positive-mass subgroup is not extremely amenable. -/
theorem not_extremelyAmenable :
    ¬ CompactFlowFixedPoint.{0, 0} (massSubgroup M.μ R.normalizedMass) :=
  massSubgroup_not_extremelyAmenable_of_age R.exists_weightedEmbedding
    R.uniformTower.uniformMassCover

/-- The positive-mass subgroup is not co-precompact in the original marked
automorphism group, assuming its transitivity on proper nonzero elements
marked zero. -/
theorem not_coprecompact
    (hTrans : ∀ a b : M.carrier,
      prebananaProperZeroMark M.μ a → prebananaProperZeroMark M.μ b →
      ∃ g : markedAutomorphisms M.μ, g • a = b)
    {p : ℕ} (hpS : p ∈ S) (hp : p.Prime) (ho : Odd p) :
    ¬ CoPrecompact (markedAutomorphisms M.μ) (massSubgroup M.μ R.normalizedMass) :=
  massSubgroup_not_coprecompact_of_age R.exists_weightedEmbedding hTrans hpS hp ho

end PositiveMassRealisation

/-- Distinct sets of allowed odd primes give nonconjugate subgroups of the
same marked automorphism group. -/
theorem positiveMassRealisations_not_conjugate {M : PrebananaCountableBooleanModel}
    {S T : AllowedOddPrimeSet} (hne : S ≠ T)
    (R : PositiveMassRealisation M S.val) (Q : PositiveMassRealisation M T.val) :
    ¬ ∃ g : ConjAct (markedAutomorphisms M.μ),
      g • massSubgroup M.μ R.normalizedMass = massSubgroup M.μ Q.normalizedMass :=
  massSubgroup_not_conjugate_of_prime_detection hne R.uniformTower.uniformMassCover
    Q.uniformTower.uniformMassCover R.massSubgroup_amenable
      (fun _ hp ho => R.prime_mem_iff hp ho) (fun _ hp ho => Q.prime_mem_iff hp ho)

/-- The marked countable limit has continuum many conjugacy classes of
closed maximal amenable subgroups. -/
theorem mk_closedMaximalAmenableConjugacyClass_of_markedLimit
    {M : PrebananaCountableBooleanModel}
    (hfinite : M.HasFiniteAmbients) (hext : M.HasFiniteExtensionProperty) :
    #(ClosedMaximalAmenableConjugacyClass (markedAutomorphisms M.μ)) = 𝔠 := by
  apply mk_closedMaximalAmenableConjugacyClass_of_massFamily M.μ
  intro S
  obtain ⟨p, hpS⟩ := S.property.1
  obtain ⟨hp, ho⟩ := S.property.2 p hpS
  obtain ⟨R⟩ := nonempty_positiveMassRealisation hfinite hext hpS hp ho
  exact ⟨R.normalizedMass, R.uniformTower.uniformMassCover, R.massSubgroup_amenable,
    fun _ hq hqo => R.prime_mem_iff hq hqo⟩

end SuccessorTree.NonPrecompact.BooleanBanana
