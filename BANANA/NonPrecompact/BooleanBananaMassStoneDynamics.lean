import BANANA.NonPrecompact.TopologicalAmenability
import BANANA.NonPrecompact.BooleanBananaStoneAction
import BANANA.NonPrecompact.OrbitCover
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Real

/-!
# Maximal amenability of mass stabilisers on Boolean Stone spaces

A mass stabiliser is closed in the marked automorphism group. If uniformly
weighted finite partitions cover the algebra and the stabiliser is transitive
on each partition's atoms, the clopen values of every invariant probability
are forced. This yields uniqueness, maximality and failure of extreme
amenability once amenability of the stabiliser is supplied.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open MeasureTheory Set MulAction
open scoped BigOperators

variable {B T : Type*} [BooleanAlgebra B]

/-- Automorphisms preserving both the marking and the real-valued mass. -/
def massSubgroup (mark : B → T) (mass : B → ℝ) :
    Subgroup (markedAutomorphisms mark) where
  carrier := {g | ∀ b, mass (g.val b) = mass b}
  one_mem' := fun _ => rfl
  mul_mem' := fun hg hh b => (hg _).trans (hh b)
  inv_mem' := by
    intro g hg b
    change mass (g.val.symm b) = mass b
    simpa only [OrderIso.apply_symm_apply] using (hg (g.val.symm b)).symm

/-- The mass stabiliser is a closed subgroup for the pointwise topology. -/
theorem isClosed_massSubgroup (mark : B → T) (mass : B → ℝ) :
    IsClosed (massSubgroup mark mass : Set (markedAutomorphisms mark)) := by
  apply isOpen_compl_iff.mp
  have hset : (massSubgroup mark mass : Set (markedAutomorphisms mark))ᶜ =
      ⋃ b : B, ⋃ c : {c : B // mass c ≠ mass b},
        {g : markedAutomorphisms mark | g.val b = c.val} := by
    ext g
    simp only [Set.mem_compl_iff, SetLike.mem_coe, Set.mem_iUnion, Set.mem_setOf_eq]
    change (¬ ∀ b, mass (g.val b) = mass b) ↔ _
    rw [not_forall]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b, ⟨g.val b, hb⟩, rfl⟩
    · rintro ⟨b, c, hc⟩
      exact ⟨b, hc.symm ▸ c.property⟩
  rw [hset]
  exact isOpen_iUnion fun b => isOpen_iUnion fun c =>
    isOpen_markedAutomorphisms_eval b c.val

/-- Every Boolean element belongs to a uniformly weighted finite subalgebra
whose atoms are transitive under the mass stabiliser. Here mass is normalised
to have total one. -/
def UniformMassCover (mark : B → T) (mass : B → ℝ) : Prop :=
  ∀ b : B, ∃ (n : ℕ) (_ : 0 < n) (f : BoundedLatticeHom (Finset (Fin n)) B)
      (s : Finset (Fin n)), f s = b ∧ mass b = (s.card : ℝ) / n ∧
    ∀ i j : Fin n, ∃ g : massSubgroup mark mass, g.val.val (f {i}) = f {j}

local instance : MeasurableSpace (BooleanSpectrum.Space B) := borel _

local instance : BorelSpace (BooleanSpectrum.Space B) := ⟨rfl⟩

/-- The normalised mass of a Boolean element under a probability on its
Stone space. -/
noncomputable def stoneMass (ν : Measure (BooleanSpectrum.Space B)) (b : B) : ℝ :=
  ν.real (BooleanSpectrum.clopens b : Set (BooleanSpectrum.Space B))

private theorem stoneMass_invariant {mark : B → T} (H : Subgroup (markedAutomorphisms mark))
    (ν : Measure (BooleanSpectrum.Space B))
    (hinv : ∀ g : H, ν.map (fun x => g • x) = ν) (g : H) (b : B) :
    stoneMass ν (g.val.val b) = stoneMass ν b := by
  have hmeas : Measurable (fun x : BooleanSpectrum.Space B => (g⁻¹ : H) • x) :=
    (continuous_const_smul (g⁻¹ : H)).measurable
  have h := congrArg (fun μ : Measure (BooleanSpectrum.Space B) =>
    μ (BooleanSpectrum.clopens b)) (hinv g⁻¹)
  change (ν.map (fun x : BooleanSpectrum.Space B => (g.val⁻¹) • x))
    (BooleanSpectrum.clopens b) = ν (BooleanSpectrum.clopens b) at h
  change Measurable (fun x : BooleanSpectrum.Space B => (g.val⁻¹) • x) at hmeas
  rw [Measure.map_apply hmeas (BooleanSpectrum.clopens b).isOpen.measurableSet,
    stoneAction_preimage_clopens] at h
  exact congrArg ENNReal.toReal h

/-- The uniform finite partitions determine the clopen values of every
invariant probability, including probabilities not assumed regular. -/
theorem stoneMass_eq_of_uniformMassCover {mark : B → T} {mass : B → ℝ}
    (hcover : UniformMassCover mark mass) (ν : Measure (BooleanSpectrum.Space B))
    [IsProbabilityMeasure ν]
    (hinv : ∀ g : massSubgroup mark mass, ν.map (fun x => g • x) = ν) :
    ∀ b : B, stoneMass ν b = mass b := by
  classical
  intro b
  obtain ⟨n, hn, f, s, rfl, hmass, htrans⟩ := hcover b
  let i₀ : Fin n := ⟨0, hn⟩
  let t := stoneMass ν (f {i₀})
  have hs (i : Fin n) : stoneMass ν (f {i}) = t := by
    obtain ⟨g, hg⟩ := htrans i i₀
    exact (stoneMass_invariant (massSubgroup mark mass) ν hinv g (f {i})).symm.trans
      (congrArg (stoneMass ν) hg)
  have aux (v : Finset (Fin n)) : stoneMass ν (f v) = (v.card : ℝ) * t := by
    induction v using Finset.induction_on with
    | empty =>
      change stoneMass ν (f ⊥) = _
      rw [map_bot]
      change ν.real (BooleanSpectrum.toSets ⊥) = _
      rw [map_bot]
      simp
    | @insert i v hi ih =>
      have hd : Disjoint ({i} : Finset (Fin n)) v :=
        Finset.disjoint_singleton_left.mpr hi
      have hdis : Disjoint (BooleanSpectrum.toSets (f {i}) : Set (BooleanSpectrum.Space B))
          (BooleanSpectrum.toSets (f v)) := by
        rw [disjoint_iff, ← map_inf, ← map_inf, hd.eq_bot, map_bot, map_bot]
      have hmeas : MeasurableSet (BooleanSpectrum.toSets (f v) : Set (BooleanSpectrum.Space B)) :=
        (BooleanSpectrum.clopens (f v)).isOpen.measurableSet
      calc
        stoneMass ν (f (insert i v)) =
            ν.real (BooleanSpectrum.toSets (f {i} ⊔ f v)) := by
              rw [← map_sup, Finset.sup_eq_union, Finset.singleton_union]; rfl
        _ = stoneMass ν (f {i}) + stoneMass ν (f v) := by
          rw [map_sup]; exact measureReal_union hdis hmeas
        _ = ((insert i v).card : ℝ) * t := by
          rw [hs, ih, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, add_mul,
            one_mul, add_comm]
  have ht := aux Finset.univ
  rw [show (Finset.univ : Finset (Fin n)) = ⊤ from rfl, map_top,
    show stoneMass ν (⊤ : B) = 1 by
      change ν.real (BooleanSpectrum.toSets (⊤ : B)) = _
      rw [map_top]; exact probReal_univ] at ht
  simp only [show (⊤ : Finset (Fin n)) = Finset.univ from rfl,
    Finset.card_univ, Fintype.card_fin] at ht
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have ht' : t = 1 / (n : ℝ) := by
    apply (eq_div_iff hnreal).2
    simpa [mul_comm] using ht.symm
  rw [hmass, aux, ht', mul_one_div]

/-- For a countable Boolean algebra the clopen values determine any two
probabilities: the clopens are a countable generating pi-system. -/
theorem stoneProbability_ext [Countable B] (μ ν : Measure (BooleanSpectrum.Space B))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ b : B, stoneMass μ b = stoneMass ν b) : μ = ν := by
  let C : Set (Set (BooleanSpectrum.Space B)) := Set.range fun b : B => BooleanSpectrum.toSets b
  have hpi : IsPiSystem C := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
    exact ⟨a ⊓ b, map_inf _ _ _⟩
  have hgen : (borel (BooleanSpectrum.Space B)) = MeasurableSpace.generateFrom C :=
    BooleanSpectrum.isTopologicalBasis_clopens.borel_eq_generateFrom
  refine Measure.ext_of_generateFrom_of_cover_subset (T := {Set.univ}) hgen hpi ?_ ?_
    (by simp) ?_ ?_
  · exact Set.singleton_subset_iff.mpr ⟨⊤, map_top _⟩
  · exact Set.countable_singleton _
  · intro s hs
    simp [Set.mem_singleton_iff.mp hs]
  · rintro _ ⟨b, rfl⟩
    have hb := h b
    change (μ (BooleanSpectrum.toSets b)).toReal = (ν (BooleanSpectrum.toSets b)).toReal at hb
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hb

/-- Any two probabilities invariant under the mass stabiliser are equal. -/
theorem invariantStoneProbability_unique [Countable B] {mark : B → T} {mass : B → ℝ}
    (hcover : UniformMassCover mark mass) (μ ν : Measure (BooleanSpectrum.Space B))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ g : massSubgroup mark mass, μ.map (fun x => g • x) = μ)
    (hν : ∀ g : massSubgroup mark mass, ν.map (fun x => g • x) = ν) :
    μ = ν :=
  stoneProbability_ext μ ν fun b =>
    (stoneMass_eq_of_uniformMassCover hcover μ hμ b).trans
      (stoneMass_eq_of_uniformMassCover hcover ν hν b).symm

/-- Every amenable supergroup of the mass stabiliser equals it. -/
theorem massSubgroup_eq_of_amenable_supergroup {B T : Type} [BooleanAlgebra B] [Nontrivial B]
    {mark : B → T} {mass : B → ℝ}
    (hcover : UniformMassCover mark mass)
    (J : Subgroup (markedAutomorphisms mark)) (hJ : massSubgroup mark mass ≤ J)
    (hAmen : IsTopologicallyAmenable J) :
    J = massSubgroup mark mass := by
  obtain ⟨ν, hprob, hinv⟩ := hAmen (BooleanSpectrum.Space B)
  letI := hprob
  have hH (g : massSubgroup mark mass) :
      ν.map (fun x : BooleanSpectrum.Space B => g • x) = ν :=
    hinv ⟨g.val, hJ g.property⟩
  have hmass := stoneMass_eq_of_uniformMassCover hcover ν hH
  apply le_antisymm _ hJ
  intro g hg b
  exact (hmass (g.val b)).symm.trans
    ((stoneMass_invariant J ν hinv ⟨g, hg⟩ b).trans (hmass b))

/-- If some element has intermediate mass then the mass stabiliser has no
fixed point in its compact Stone space. -/
theorem massSubgroup_no_stone_fixedPoint {mark : B → T} {mass : B → ℝ}
    (hcover : UniformMassCover mark mass) (b : B) (hb0 : 0 < mass b)
    (hb1 : mass b < 1) :
    ¬ ∃ x : BooleanSpectrum.Space B, ∀ g : massSubgroup mark mass, g • x = x := by
  rintro ⟨x, hx⟩
  let ν := Measure.dirac x
  have hν (g : massSubgroup mark mass) : ν.map (fun y => g • y) = ν := by
    rw [Measure.map_dirac' (continuous_const_smul g).measurable, hx g]
  have h := stoneMass_eq_of_uniformMassCover hcover ν hν b
  change (Measure.dirac x).real (BooleanSpectrum.clopens b) = mass b at h
  rw [measureReal_def, Measure.dirac_apply' x (BooleanSpectrum.clopens b).isOpen.measurableSet] at h
  by_cases hb : x ∈ (BooleanSpectrum.clopens b : Set (BooleanSpectrum.Space B))
  · simp only [Set.indicator_of_mem hb, Pi.one_apply, ENNReal.toReal_one] at h
    linarith
  · simp only [Set.indicator_of_notMem hb, ENNReal.toReal_zero] at h
    linarith

/-- Conjugate amenable mass stabilisers with uniform covers have the same
sets of clopen masses. -/
theorem massRange_eq_of_conjugate {B T : Type} [BooleanAlgebra B] [Nontrivial B]
    {mark : B → T} {m₁ m₂ : B → ℝ}
    (h₁ : UniformMassCover mark m₁) (h₂ : UniformMassCover mark m₂)
    (hAmen : IsTopologicallyAmenable (massSubgroup mark m₁))
    (g : markedAutomorphisms mark)
    (hconj : ∀ k : markedAutomorphisms mark,
      k ∈ massSubgroup mark m₁ ↔ g * k * g⁻¹ ∈ massSubgroup mark m₂) :
    Set.range m₁ = Set.range m₂ := by
  obtain ⟨ν, hprob, hinv⟩ := hAmen (BooleanSpectrum.Space B)
  letI := hprob
  let μ := ν.map (fun x : BooleanSpectrum.Space B => g • x)
  have hμ (h : massSubgroup mark m₂) : μ.map (fun x => h • x) = μ := by
    let k : massSubgroup mark m₁ :=
      ⟨g⁻¹ * h.val * g, (hconj _).2 (by simpa [mul_assoc] using h.property)⟩
    have hg : Measurable (fun x : BooleanSpectrum.Space B => g • x) :=
      (continuous_const_smul g).measurable
    have hh : Measurable (fun x : BooleanSpectrum.Space B => h.val • x) :=
      (continuous_const_smul h.val).measurable
    have hk : Measurable (fun x : BooleanSpectrum.Space B => k.val • x) :=
      (continuous_const_smul k.val).measurable
    have hc : (fun x : BooleanSpectrum.Space B => h.val • x) ∘ (fun x => g • x) =
        (fun x : BooleanSpectrum.Space B => g • x) ∘ (fun x => k.val • x) := by
      funext x
      change h.val • (g • x) = g • (k.val • x)
      rw [← mul_smul, ← mul_smul]
      congr 1
      simp [k, mul_assoc]
    change (ν.map (fun x : BooleanSpectrum.Space B => g • x)).map
      (fun x => h.val • x) = μ
    rw [Measure.map_map hh hg, hc, ← Measure.map_map hg hk]
    change (ν.map (fun x : BooleanSpectrum.Space B => k • x)).map _ = μ
    rw [hinv k]
  have hm (b : B) : m₁ b = m₂ (g.val b) := by
    rw [← stoneMass_eq_of_uniformMassCover h₁ ν hinv b,
      ← stoneMass_eq_of_uniformMassCover h₂ μ hμ (g.val b)]
    change (ν (BooleanSpectrum.clopens b)).toReal =
      ((ν.map (fun x : BooleanSpectrum.Space B => g • x))
        (BooleanSpectrum.clopens (g.val b))).toReal
    rw [Measure.map_apply (continuous_const_smul g).measurable
      (BooleanSpectrum.clopens (g.val b)).isOpen.measurableSet,
      stoneAction_preimage_clopens, g.val.symm_apply_apply]
  ext r
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨g.val b, (hm b).symm⟩
  · rintro ⟨b, rfl⟩
    exact ⟨g.val.symm b, (hm _).trans (congrArg m₂ (g.val.apply_symm_apply b))⟩

/-- Infinitely many mass values in a single marked orbit rule out a finite
double-coset cover at its point stabiliser. -/
theorem massSubgroup_no_doubleCosetCover {mark : B → T} {mass : B → ℝ} (a : B)
    (x : ℕ → orbit (markedAutomorphisms mark) a)
    (hx : Function.Injective (fun n => mass (x n).val)) :
    ¬ ∃ F : Finset (markedAutomorphisms mark), ∀ g : markedAutomorphisms mark,
      ∃ f ∈ F, ∃ (u : stabilizer (markedAutomorphisms mark) a)
        (h : massSubgroup mark mass), g = u.val * f * h.val := by
  classical
  intro hcover
  obtain ⟨R, hR⟩ := (exists_finset_doubleCosetCover_iff_orbit_representatives
    (massSubgroup mark mass) a).mp hcover
  let S := R.image (fun r => mass r.val)
  have hm (n : ℕ) : mass (x n).val ∈ S := by
    obtain ⟨r, hr, hxr⟩ := hR (x n)
    obtain ⟨h, hh⟩ := mem_orbit_iff.mp hxr
    refine Finset.mem_image.mpr ⟨r, hr, ?_⟩
    exact (h.property r.val).symm.trans (congrArg mass hh)
  exact not_injective_infinite_finite (fun n => (⟨mass (x n).val, hm n⟩ : S))
    (fun i j e => hx (congrArg Subtype.val e))

/-- Infinitely many different masses in one ambient orbit prevent
co-precompactness in the pointwise topology. -/
theorem massSubgroup_not_coprecompact {mark : B → T} {mass : B → ℝ} (a : B)
    (x : ℕ → orbit (markedAutomorphisms mark) a)
    (hx : Function.Injective (fun n => mass (x n).val)) :
    ¬ CoPrecompact (markedAutomorphisms mark) (massSubgroup mark mass) := by
  intro h
  have hopen : IsOpen (stabilizer (markedAutomorphisms mark) a : Set (markedAutomorphisms mark)) := by
    change IsOpen {g : markedAutomorphisms mark | g.val a = a}
    exact isOpen_markedAutomorphisms_eval (mark := mark) a a
  obtain ⟨F, hF⟩ := h _ (hopen.mem_nhds (stabilizer _ a).one_mem)
  apply massSubgroup_no_doubleCosetCover a x hx
  exact ⟨F, fun g => by
    obtain ⟨f, hf, u, hu, k, hg⟩ := hF g
    exact ⟨f, hf, ⟨u, hu⟩, k, hg⟩⟩

end SuccessorTree.NonPrecompact.BooleanBanana
