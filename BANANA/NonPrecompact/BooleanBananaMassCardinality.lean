import BANANA.NonPrecompact.BooleanBananaMassStoneDynamics
import BANANA.NonPrecompact.BooleanBananaMassRangeRealisation
import BANANA.NonPrecompact.BooleanBananaPositiveMassLimitGroups
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Topology.Instances.Discrete

/-!
# Cardinality of maximal amenable conjugacy classes

In a second-countable group, a closed subgroup is determined by the members
of a fixed countable basis contained in its open complement. In the marked
Boolean automorphism group a family of amenable mass stabilisers with uniform
covers and prime-detecting mass ranges gives the matching lower bound.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open Cardinal MulAction Set TopologicalSpace
open scoped Cardinal Pointwise

/-- The nonempty sets of allowed odd primes indexing the positive masses. -/
abbrev AllowedOddPrimeSet := {S : Set ℕ // S.Nonempty ∧ ∀ p ∈ S, p.Prime ∧ Odd p}

/-- There are continuum many nonempty sets of odd primes. -/
theorem mk_allowedOddPrimeSet : #AllowedOddPrimeSet = 𝔠 := by
  let P := {p : ℕ | p.Prime ∧ 5 ≤ p}
  have hP : P.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨b, hb⟩
    obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (max 5 (b + 1))
    have h5 : 5 ≤ p := (le_max_left 5 (b + 1)).trans hle
    have hp' : p ∈ P := ⟨hp, h5⟩
    have hbp := hb hp'
    have hnext := (le_max_right 5 (b + 1)).trans hle
    omega
  let : Infinite P := hP.to_subtype
  let e : ℕ → ℕ := fun n => (Infinite.natEmbedding P n).val
  have he : Function.Injective e := Subtype.val_injective.comp (Infinite.natEmbedding P).injective
  have heP (n : ℕ) : e n ∈ P := (Infinite.natEmbedding P n).property
  let f (S : Set ℕ) : AllowedOddPrimeSet := ⟨insert 3 (e '' S), by
    refine ⟨⟨3, mem_insert _ _⟩, ?_⟩
    intro p hp
    rcases mem_insert_iff.mp hp with rfl | ⟨n, _, rfl⟩
    · decide
    · exact ⟨(heP n).1, (heP n).1.odd_of_ne_two (by have := (heP n).2; omega)⟩⟩
  have hf : Function.Injective f := by
    intro S T h
    have hsets : insert 3 (e '' S) = insert 3 (e '' T) := congrArg Subtype.val h
    ext n
    have hnot : e n ≠ 3 := by have := (heP n).2; omega
    have hmem (U : Set ℕ) : e n ∈ insert 3 (e '' U) ↔ n ∈ U := by
      rw [mem_insert_iff, or_iff_right hnot]
      exact he.mem_set_image
    rw [← hmem S, hsets, hmem T]
  apply le_antisymm
  · exact (mk_le_of_injective (f := (Subtype.val : AllowedOddPrimeSet → Set ℕ))
      Subtype.val_injective).trans_eq mk_set_nat
  · exact mk_set_nat ▸ mk_le_of_injective hf

/-- Closed amenable subgroups maximal among all amenable subgroups. -/
abbrev ClosedMaximalAmenableSubgroup (G : Type*) [Group G] [TopologicalSpace G] :=
  {H : Subgroup G // IsClosed (H : Set G) ∧ IsTopologicallyAmenable H ∧
    ∀ J : Subgroup G, H ≤ J → IsTopologicallyAmenable J → J = H}

/-- Conjugacy classes of closed maximal amenable subgroups, using the
ambient group's conjugation action on subgroups. -/
abbrev ClosedMaximalAmenableConjugacyClass (G : Type*) [Group G] [TopologicalSpace G] :=
  Quotient (Setoid.comap (Subtype.val : ClosedMaximalAmenableSubgroup G → Subgroup G)
    (orbitRel (ConjAct G) (Subgroup G)))

/-- In a second-countable group there are at most continuum many closed
subgroups. Each is coded by its open complement in the countable basis. -/
theorem mk_closedSubgroup_le_continuum (G : Type*) [Group G] [TopologicalSpace G]
    [SecondCountableTopology G] : #{H : Subgroup G // IsClosed (H : Set G)} ≤ 𝔠 := by
  let b := countableBasis G
  let : Countable b := countable_countableBasis G
  let code (H : {H : Subgroup G // IsClosed (H : Set G)}) : Set b :=
    {U | U.val ⊆ (H.val : Set G)ᶜ}
  have hi : Function.Injective code := by
    intro H K he
    have hs : (H.val : Set G)ᶜ = (K.val : Set G)ᶜ := by
      have subset_of_code_subset
          (M N : {H : Subgroup G // IsClosed (H : Set G)}) (h : code M ⊆ code N) :
          (M.val : Set G)ᶜ ⊆ (N.val : Set G)ᶜ := by
        intro x hx
        obtain ⟨U, hU, hxU, hUM⟩ :=
          (isBasis_countableBasis G).exists_subset_of_mem_open hx M.property.isOpen_compl
        exact h (show (⟨U, hU⟩ : b) ∈ code M from hUM) hxU
      exact Set.Subset.antisymm (subset_of_code_subset H K he.le)
        (subset_of_code_subset K H he.ge)
    exact Subtype.ext (SetLike.coe_injective (compl_injective hs))
  calc
    _ ≤ #(Set b) := mk_le_of_injective hi
    _ = 2 ^ #b := mk_set
    _ ≤ 2 ^ ℵ₀ := power_le_power_left (by simp) mk_le_aleph0
    _ = 𝔠 := two_power_aleph0

/-- A second-countable group has at most continuum many conjugacy classes
of closed maximal amenable subgroups. -/
theorem mk_closedMaximalAmenableConjugacyClass_le_continuum
    (G : Type*) [Group G] [TopologicalSpace G] [SecondCountableTopology G] :
    #(ClosedMaximalAmenableConjugacyClass G) ≤ 𝔠 := by
  let f (H : ClosedMaximalAmenableSubgroup G) :
      {H : Subgroup G // IsClosed (H : Set G)} := ⟨H.val, H.property.1⟩
  have hf : Function.Injective f := by
    intro H K h
    exact Subtype.ext (congrArg (fun J : {H : Subgroup G // IsClosed (H : Set G)} => J.val) h)
  exact mk_quotient_le.trans
    ((mk_le_of_injective hf).trans (mk_closedSubgroup_le_continuum G))

/-- The pointwise topology on the automorphisms of a countable marked
Boolean algebra is second countable. -/
theorem markedAutomorphisms_secondCountableTopology {B T : Type*} [BooleanAlgebra B]
    [Countable B] (mark : B → T) : SecondCountableTopology (markedAutomorphisms mark) := by
  let : Countable (WithDiscreteTopology B) :=
    (WithTopology.toTopology_surjective (⊥ : TopologicalSpace B)).countable
  let e (g : markedAutomorphisms mark) : B → WithDiscreteTopology B :=
    fun b => WithTopology.toTopology ⊥ (g.val b)
  change @SecondCountableTopology _ (TopologicalSpace.induced e inferInstance)
  exact secondCountableTopology_induced _ _ e

/-- Distinct sets of allowed primes determine nonconjugate amenable mass
stabilisers whenever their uniform covers and range detection are known. -/
theorem massSubgroup_not_conjugate_of_prime_detection
    {B α : Type} [BooleanAlgebra B] [Nontrivial B] {mark : B → α}
    {S T : AllowedOddPrimeSet} {m₁ m₂ : B → ℝ} (hne : S ≠ T)
    (hcover₁ : UniformMassCover mark m₁) (hcover₂ : UniformMassCover mark m₂)
    (hAmen₁ : IsTopologicallyAmenable (massSubgroup mark m₁))
    (hdetect₁ : ∀ p : ℕ, p.Prime → Odd p →
      (p ∈ S.val ↔ 1 / (2 * (p : ℝ)) ∈ Set.range m₁))
    (hdetect₂ : ∀ p : ℕ, p.Prime → Odd p →
      (p ∈ T.val ↔ 1 / (2 * (p : ℝ)) ∈ Set.range m₂)) :
    ¬ ∃ g : ConjAct (markedAutomorphisms mark), g • massSubgroup mark m₁ = massSubgroup mark m₂ := by
  rintro ⟨g, hg⟩
  apply hne
  apply Subtype.ext
  apply positiveMassPrimeSets_eq_of_range_eq m₁ m₂ S.property.2 T.property.2 hdetect₁ hdetect₂
  apply massRange_eq_of_conjugate hcover₁ hcover₂ hAmen₁ (ConjAct.ofConjAct g)
  intro k
  rw [← ConjAct.smul_def, ← hg]
  exact Subgroup.smul_mem_pointwise_smul_iff.symm

/-- A prime-indexed family of mass stabilisers gives continuum many conjugacy
classes of closed maximal amenable subgroups of the pointwise automorphism
group. The mass functions here are normalised to have total one. -/
theorem mk_closedMaximalAmenableConjugacyClass_of_massFamily
    {B T : Type} [BooleanAlgebra B] [Nontrivial B] [Countable B] (mark : B → T)
    (hFamily : ∀ S : AllowedOddPrimeSet, ∃ mass : B → ℝ,
      UniformMassCover mark mass ∧ IsTopologicallyAmenable (massSubgroup mark mass) ∧
        ∀ p : ℕ, p.Prime → Odd p →
          (p ∈ S.val ↔ 1 / (2 * (p : ℝ)) ∈ Set.range mass)) :
    #(ClosedMaximalAmenableConjugacyClass (markedAutomorphisms mark)) = 𝔠 := by
  let := markedAutomorphisms_secondCountableTopology mark
  apply le_antisymm (mk_closedMaximalAmenableConjugacyClass_le_continuum _)
  classical
  choose mass hmass using hFamily
  let candidate (S : AllowedOddPrimeSet) : ClosedMaximalAmenableSubgroup (markedAutomorphisms mark) :=
    ⟨massSubgroup mark (mass S), isClosed_massSubgroup mark (mass S), (hmass S).2.1,
      fun J hJ hAmen => massSubgroup_eq_of_amenable_supergroup (hmass S).1 J hJ hAmen⟩
  let f (S : AllowedOddPrimeSet) : ClosedMaximalAmenableConjugacyClass (markedAutomorphisms mark) :=
    Quotient.mk _ (candidate S)
  have hf : Function.Injective f := by
    intro S T eq
    obtain ⟨g, hg⟩ := Quotient.exact eq
    change g • massSubgroup mark (mass T) = massSubgroup mark (mass S) at hg
    by_contra hne
    exact (massSubgroup_not_conjugate_of_prime_detection (Ne.symm hne)
      (hmass T).1 (hmass S).1 (hmass T).2.1 (hmass T).2.2 (hmass S).2.2) ⟨g, hg⟩
  exact mk_allowedOddPrimeSet ▸ mk_le_of_injective hf

/-- A coherent rational-mass tower and its finite age for each allowed
prime set give the continuum of conjugacy classes on one fixed algebra. -/
theorem mk_closedMaximalAmenableConjugacyClass_of_massTowers
    {B : Type} [BooleanAlgebra B] [Nontrivial B] [Countable B] (mark : B → ZMod 2)
    (hFamily : ∀ S : AllowedOddPrimeSet, ∃ (ρ : B → ℚ) (J : ℕ → Type)
      (_ : ∀ n, Fintype (J n)) (_ : ∀ n, DecidableEq (J n)) (_ : ∀ n, Nonempty (J n)),
      Nonempty (UniformMassTower J mark (fun x => (ρ x : ℝ) / 2)) ∧
      (∀ (A : Type) [BooleanAlgebra A] [Fintype A]
        (μ : A → ZMod 2) (η : A → ℚ), IsFinitePositiveMass S.val μ η →
        ∃ f : BoundedLatticeHom A B, Function.Injective f ∧
          (∀ a, mark (f a) = μ a) ∧ (∀ a, ρ (f a) = η a)) ∧
      (∀ b : B, ∃ (A : Type) (_ : BooleanAlgebra A) (_ : Fintype A)
        (f : BoundedLatticeHom A B) (a : A),
        IsFinitePositiveMass S.val (mark ∘ f) (ρ ∘ f) ∧ f a = b)) :
    #(ClosedMaximalAmenableConjugacyClass (markedAutomorphisms mark)) = 𝔠 := by
  apply mk_closedMaximalAmenableConjugacyClass_of_massFamily mark
  intro S
  obtain ⟨ρ, J, hFin, hDec, hNonempty, ⟨tower⟩, hAge, hCover⟩ := hFamily S
  let := hFin
  let := hDec
  let := hNonempty
  exact ⟨fun x => (ρ x : ℝ) / 2, tower.uniformMassCover, tower.massSubgroup_amenable,
    fun _ hp ho => positiveMass_prime_mem_iff_of_age hAge hCover hp ho⟩

end SuccessorTree.NonPrecompact.BooleanBanana
