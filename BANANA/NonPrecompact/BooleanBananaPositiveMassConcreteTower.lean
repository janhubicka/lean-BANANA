import BANANA.NonPrecompact.BooleanBananaPositiveMassLimitGroups
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Order.BooleanSubalgebra

/-!
# The concrete uniform positive-mass Boolean tower

Finite-prefix cylinders in the product of a two-point space and the
successive child-label spaces form the countable Boolean algebra.
Allowed odd refinement indices make rational mass and parity independent
of the level at which the cylinder is presented.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open Set BigOperators
open scoped Classical

/-- An increasing cofinal chain of allowed denominators, with its uniform
refinement indices. -/
structure PositiveMassDenominatorTower (S : Set ℕ) where
  D : ℕ → ℕ
  children : ℕ → ℕ
  base : D 0 = 1
  allowed : ∀ n, D n ∈ positiveMassDenominators S
  children_allowed : ∀ n, children n ∈ positiveMassDenominators S
  children_large : ∀ n, 1 < children n
  succ_mul : ∀ n, D (n + 1) = D n * children n
  cofinal : ∀ d ∈ positiveMassDenominators S, ∃ n, d ∣ D n

/-- A nonempty set of allowed odd primes supplies the denominator tower. -/
theorem nonempty_positiveMassDenominatorTower {S : Set ℕ} {p : ℕ}
    (hpS : p ∈ S) (hp : p.Prime) (hpOdd : Odd p) :
    Nonempty (PositiveMassDenominatorTower S) := by
  obtain ⟨D, hbase, hallowed, hsucc, hcofinal⟩ :=
    exists_positive_mass_denominator_chain hpS hp hpOdd
  choose k hk hkLarge hDk using hsucc
  exact ⟨⟨D, k, hbase, hallowed, hk, hkLarge, hDk, hcofinal⟩⟩

namespace PositiveMassDenominatorTower

variable {S : Set ℕ} (T : PositiveMassDenominatorTower S)

theorem denominator_pos (n : ℕ) : 0 < T.D n := by
  obtain ⟨j, hj⟩ := (T.allowed n).1
  omega

theorem denominator_dvd {m n : ℕ} (h : m ≤ n) : T.D m ∣ T.D n := by
  induction h with
  | refl => exact dvd_rfl
  | step _ ih => rw [T.succ_mul]; exact ih.trans (Nat.dvd_mul_right _ _)

/-- Infinite paths, starting with the two atoms of mass one. -/
abbrev Path : Type := Fin 2 × ((i : ℕ) → Fin (T.children i))

/-- Atom labels at level `n`. -/
abbrev Label (n : ℕ) : Type := Fin 2 × ((i : Fin n) → Fin (T.children i))

instance (n : ℕ) : Nonempty (T.Label n) :=
  ⟨(0, fun i => ⟨0, Nat.zero_lt_of_lt (T.children_large i)⟩)⟩

/-- Truncate an infinite path to its level-`n` label. -/
def pathPrefix (n : ℕ) (x : T.Path) : T.Label n := (x.1, fun i => x.2 i)

theorem prefix_surjective (n : ℕ) : Function.Surjective (T.pathPrefix n) := by
  intro x
  use (x.1, fun i => if h : i < n then x.2 ⟨i, h⟩ else
    ⟨0, Nat.zero_lt_of_lt (T.children_large i)⟩)
  apply Prod.ext
  · rfl
  · funext i
    simp [pathPrefix, i.isLt]

/-- The prefix projection between finite levels. -/
def parent (m n : ℕ) (h : m ≤ n) (x : T.Label n) : T.Label m :=
  (x.1, fun i => x.2 (Fin.castLE h i))

@[simp] theorem parent_prefix (m n : ℕ) (h : m ≤ n) (x : T.Path) :
    T.parent m n h (T.pathPrefix n x) = T.pathPrefix m x := rfl

/-- Separating the last child label identifies the next level with a
uniform product. -/
def split (n : ℕ) : T.Label (n + 1) ≃ T.Label n × Fin (T.children n) where
  toFun x := (T.parent n (n + 1) (Nat.le_succ n) x, x.2 (Fin.last n))
  invFun x := (x.1.1, Fin.snoc x.1.2 x.2)
  left_inv x := by
    apply Prod.ext
    · rfl
    · change Fin.snoc (Fin.init x.2) (x.2 (Fin.last n)) = x.2
      exact Fin.snoc_init_self x.2
  right_inv x := by
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · change Fin.init (Fin.snoc (α := fun i : Fin (n + 1) => Fin (T.children i))
          x.1.2 x.2) = x.1.2
        exact Fin.init_snoc _ _
    · change Fin.snoc (α := fun i : Fin (n + 1) => Fin (T.children i))
        x.1.2 x.2 (Fin.last n) = x.2
      exact Fin.snoc_last _ _

theorem stage_card (n : ℕ) : Fintype.card (T.Label n) = 2 * T.D n := by
  induction n with
  | zero => simp [Label, T.base]
  | succ n ih =>
    rw [Fintype.card_congr (T.split n), Fintype.card_prod, Fintype.card_fin, ih,
      T.succ_mul, Nat.mul_assoc]

/-- Inclusion from one finite powerset to a later one by inverse image
of the prefix projection. -/
def lift (m n : ℕ) (h : m ≤ n) : BoundedLatticeHom (Finset (T.Label m)) (Finset (T.Label n)) :=
  positiveMassAtomPreimage (T.parent m n h)

theorem lift_injective (m n : ℕ) (h : m ≤ n) : Function.Injective (T.lift m n h) := by
  apply positiveMassAtomPreimage_injective
  intro x
  obtain ⟨p, rfl⟩ := T.prefix_surjective m x
  exact ⟨T.pathPrefix n p, rfl⟩

private def cylinderSet (n : ℕ) (s : Finset (T.Label n)) : Set T.Path :=
  {x | T.pathPrefix n x ∈ s}

private theorem cylinderSet_injective (n : ℕ) : Function.Injective (T.cylinderSet n) := by
  intro s t h
  ext x
  obtain ⟨p, rfl⟩ := T.prefix_surjective n x
  exact Set.ext_iff.mp h p

private theorem cylinderSet_lift {m n : ℕ} (h : m ≤ n) (s : Finset (T.Label m)) :
    T.cylinderSet n (T.lift m n h s) = T.cylinderSet m s := by
  ext x
  simp [cylinderSet, lift, positiveMassAtomPreimage]

/-- The concrete Boolean subalgebra of all finite-prefix cylinders. -/
noncomputable def cylinderSubalgebra : BooleanSubalgebra (Set T.Path) where
  carrier := {x | ∃ n s, x = T.cylinderSet n s}
  bot_mem' := ⟨0, ∅, by ext x; simp [cylinderSet]⟩
  compl_mem' := by
    rintro _ ⟨n, s, rfl⟩
    exact ⟨n, Finset.univ \ s, by ext x; simp [cylinderSet]⟩
  supClosed' := by
    rintro _ ⟨m, s, rfl⟩ _ ⟨n, t, rfl⟩
    let N := max m n
    let s' := T.lift m N (le_max_left _ _) s
    let t' := T.lift n N (le_max_right _ _) t
    refine ⟨N, s' ∪ t', ?_⟩
    rw [← T.cylinderSet_lift (le_max_left m n) s,
      ← T.cylinderSet_lift (le_max_right m n) t]
    ext x
    simp [cylinderSet, s', t', N]
  infClosed' := by
    rintro _ ⟨m, s, rfl⟩ _ ⟨n, t, rfl⟩
    let N := max m n
    let s' := T.lift m N (le_max_left _ _) s
    let t' := T.lift n N (le_max_right _ _) t
    refine ⟨N, s' ∩ t', ?_⟩
    rw [← T.cylinderSet_lift (le_max_left m n) s,
      ← T.cylinderSet_lift (le_max_right m n) t]
    ext x
    simp [cylinderSet, s', t', N]

/-- The Boolean algebra carrier of the uniform tower. -/
abbrev Cylinder : Type := T.cylinderSubalgebra

/-- The finite stages as actual bounded-lattice embeddings. -/
noncomputable def stage (n : ℕ) : BoundedLatticeHom (Finset (T.Label n)) T.Cylinder where
  toFun s := ⟨T.cylinderSet n s, ⟨n, s, rfl⟩⟩
  map_bot' := by apply Subtype.ext; ext x; simp [cylinderSet]
  map_top' := by apply Subtype.ext; ext x; simp [cylinderSet]
  map_sup' s t := by apply Subtype.ext; ext x; simp [cylinderSet]
  map_inf' s t := by apply Subtype.ext; ext x; simp [cylinderSet]

theorem stage_injective (n : ℕ) : Function.Injective (T.stage n) :=
  fun _ _ h => T.cylinderSet_injective n (congrArg Subtype.val h)

theorem stage_lift {m n : ℕ} (h : m ≤ n) (s : Finset (T.Label m)) :
    T.stage n (T.lift m n h s) = T.stage m s :=
  Subtype.ext (T.cylinderSet_lift h s)

theorem covers (x : T.Cylinder) : ∃ n s, T.stage n s = x := by
  obtain ⟨n, s, hs⟩ := x.property
  exact ⟨n, s, Subtype.ext hs.symm⟩

instance : Countable T.Cylinder := by
  let f : (Σ n : ℕ, Finset (T.Label n)) → T.Cylinder := fun a => T.stage a.1 a.2
  have hf : Function.Surjective f := fun x =>
    let ⟨n, s, h⟩ := T.covers x
    ⟨⟨n, s⟩, h⟩
  have hc := Set.countable_range f
  rw [Set.range_eq_univ.mpr hf] at hc
  exact (Set.countable_univ_iff).mp hc

instance : Nontrivial T.Cylinder := by
  letI : Nontrivial (Finset (T.Label 0)) := inferInstance
  exact (T.stage_injective 0).nontrivial

private theorem lift_succ_card (n : ℕ) (s : Finset (T.Label n)) :
    (T.lift n (n + 1) (Nat.le_succ n) s).card = s.card * T.children n := by
  let e := T.split n
  have he : (T.lift n (n + 1) (Nat.le_succ n) s).map e.toEmbedding =
      s ×ˢ (Finset.univ : Finset (Fin (T.children n))) := by
    ext x
    rw [Finset.mem_map_equiv]
    change e.symm x ∈ Finset.univ.filter (fun j => (e j).1 ∈ s) ↔ _
    simp [Finset.mem_product]
  rw [← Finset.card_map e.toEmbedding, he, Finset.card_product,
    Finset.card_univ, Fintype.card_fin]

private theorem lift_succ {m n : ℕ} (h : m ≤ n) (s : Finset (T.Label m)) :
    T.lift m (n + 1) (Nat.le_succ_of_le h) s =
      T.lift n (n + 1) (Nat.le_succ n) (T.lift m n h s) := by
  apply T.stage_injective (n + 1)
  rw [T.stage_lift, T.stage_lift, T.stage_lift]

theorem lift_mass {m n : ℕ} (h : m ≤ n) (s : Finset (T.Label m)) :
    ((T.lift m n h s).card : ℚ) / T.D n = (s.card : ℚ) / T.D m := by
  induction h with
  | refl =>
    have hs : T.lift m m (le_refl m) s = s := by
      apply T.stage_injective m
      exact T.stage_lift _ _
    rw [hs]
  | @step n h ih =>
    rw [T.lift_succ h, T.lift_succ_card, T.succ_mul, Nat.cast_mul, Nat.cast_mul,
      mul_div_mul_right _ _ (by
        exact_mod_cast (Nat.zero_lt_of_lt (T.children_large n)).ne'), ih]

theorem lift_mark {m n : ℕ} (h : m ≤ n) (s : Finset (T.Label m)) :
    ((T.lift m n h s).card : ZMod 2) = (s.card : ZMod 2) := by
  induction h with
  | refl =>
    have hs : T.lift m m (le_refl m) s = s := by
      apply T.stage_injective m
      exact T.stage_lift _ _
    rw [hs]
  | @step n h ih =>
    rw [T.lift_succ h, T.lift_succ_card, Nat.cast_mul, ih,
      (T.children_allowed n).1.natCast_zmod_two, mul_one]

private theorem commonStage_eq {m n : ℕ} {s : Finset (T.Label m)} {t : Finset (T.Label n)}
    (h : T.stage m s = T.stage n t) :
    T.lift m (max m n) (le_max_left _ _) s = T.lift n (max m n) (le_max_right _ _) t := by
  apply T.stage_injective (max m n)
  rwa [T.stage_lift, T.stage_lift]

private theorem presentation_weights {m n : ℕ} {s : Finset (T.Label m)} {t : Finset (T.Label n)}
    (h : T.stage m s = T.stage n t) :
    (s.card : ℚ) / T.D m = (t.card : ℚ) / T.D n ∧
      (s.card : ZMod 2) = (t.card : ZMod 2) := by
  have he := T.commonStage_eq h
  constructor
  · rw [← T.lift_mass (le_max_left m n) s, ← T.lift_mass (le_max_right m n) t, he]
  · rw [← T.lift_mark (le_max_left m n) s, ← T.lift_mark (le_max_right m n) t, he]

/-- The rational mass of a cylinder, with total mass two. -/
noncomputable def mass (x : T.Cylinder) : ℚ :=
  ((T.covers x).choose_spec.choose.card : ℚ) / T.D (T.covers x).choose

/-- The parity marking of a cylinder. -/
noncomputable def mark (x : T.Cylinder) : ZMod 2 :=
  (T.covers x).choose_spec.choose.card

@[simp] theorem mass_stage (n : ℕ) (s : Finset (T.Label n)) :
    T.mass (T.stage n s) = (s.card : ℚ) / T.D n :=
  (T.presentation_weights (T.covers (T.stage n s)).choose_spec.choose_spec).1

@[simp] theorem mark_stage (n : ℕ) (s : Finset (T.Label n)) :
    T.mark (T.stage n s) = (s.card : ZMod 2) :=
  (T.presentation_weights (T.covers (T.stage n s)).choose_spec.choose_spec).2

/-- Each stage with the restricted mark and mass belongs to the finite
positive-mass class. -/
theorem stage_weighted (n : ℕ) :
    IsFinitePositiveMass S (T.mark ∘ T.stage n) (T.mass ∘ T.stage n) := by
  simpa only [Function.comp_def, T.mass_stage, T.mark_stage] using
    (positiveMass_uniformStage (J := T.Label n) (T.allowed n) (T.stage_card n))

/-- Every finite family is contained in a single actual stage. -/
theorem exists_finiteAmbient (s : Finset T.Cylinder) :
    ∃ n, ∀ x ∈ s, x ∈ Set.range (T.stage n) := by
  classical
  let level (x : T.Cylinder) := (T.covers x).choose
  let n := s.sup level
  refine ⟨n, fun x hx => ?_⟩
  obtain ⟨t, ht⟩ := (T.covers x).choose_spec
  exact ⟨T.lift (level x) n (Finset.le_sup hx) t, (T.stage_lift _ _).trans ht⟩

/-- The concrete cylinder algebra instantiates the uniform tower used for
the finite subgroup and Stone measure arguments. -/
noncomputable def uniformTower :
    UniformMassTower T.Label T.mark (fun x => (T.mass x : ℝ) / 2) where
  children := T.children
  split := T.split
  stage := T.stage
  stage_injective := T.stage_injective
  stage_step := fun n s => T.stage_lift (Nat.le_succ n) s
  covers := T.covers
  mass_stage n s := by
    rw [T.mass_stage, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast, T.stage_card,
      Nat.cast_mul, Nat.cast_ofNat, div_div, mul_comm (T.D n : ℝ)]
  mark_stage := T.mark_stage

/-- A finite Boolean embedding into the cylinder algebra factors through
one of the actual finite stages. -/
theorem exists_stageFactor {A : Type} [BooleanAlgebra A] [Fintype A]
    (f : BoundedLatticeHom A T.Cylinder) (hf : Function.Injective f) :
    ∃ n, ∃ g : BoundedLatticeHom A (Finset (T.Label n)), Function.Injective g ∧
      ∀ a, T.stage n (g a) = f a := by
  classical
  obtain ⟨n, hn⟩ := T.exists_finiteAmbient (Finset.univ.image f)
  exact ⟨n, T.uniformTower.factor_toStage f hf (fun a =>
    hn (f a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))⟩

@[simp] theorem mark_bot : T.mark ⊥ = 0 := by
  rw [← map_bot (T.stage 0), T.mark_stage]
  rfl

@[simp] theorem mark_top : T.mark ⊤ = 0 := by
  rw [← map_top (T.stage 0), T.mark_stage]
  change (Fintype.card (T.Label 0) : ZMod 2) = 0
  rw [T.stage_card, T.base]
  decide

@[simp] theorem mass_bot : T.mass ⊥ = 0 := by
  rw [← map_bot (T.stage 0), T.mass_stage]
  simp

@[simp] theorem mass_top : T.mass ⊤ = 2 := by
  rw [← map_top (T.stage 0), T.mass_stage]
  change (Fintype.card (T.Label 0) : ℚ) / T.D 0 = 2
  rw [T.stage_card, T.base]
  norm_num

private theorem disjointStage {x y : T.Cylinder} (h : x ⊓ y = ⊥) :
    ∃ n, ∃ s t : Finset (T.Label n),
      T.stage n s = x ∧ T.stage n t = y ∧ s ⊓ t = ⊥ := by
  classical
  obtain ⟨n, hn⟩ := T.exists_finiteAmbient {x, y}
  obtain ⟨s, hs⟩ := hn x (by simp)
  obtain ⟨t, ht⟩ := hn y (by simp)
  refine ⟨n, s, t, hs, ht, T.stage_injective n ?_⟩
  rwa [map_inf, hs, ht, map_bot]

/-- The marking is disjoint-additive on the actual cylinder algebra. -/
theorem mark_add {x y : T.Cylinder} (h : x ⊓ y = ⊥) :
    T.mark (x ⊔ y) = T.mark x + T.mark y := by
  obtain ⟨n, s, t, rfl, rfl, hst⟩ := T.disjointStage h
  rw [← map_sup (T.stage n)]
  exact (T.stage_weighted n).mark_add s t hst

/-- The rational mass is disjoint-additive on the actual cylinder algebra. -/
theorem mass_add {x y : T.Cylinder} (h : x ⊓ y = ⊥) :
    T.mass (x ⊔ y) = T.mass x + T.mass y := by
  obtain ⟨n, s, t, rfl, rfl, hst⟩ := T.disjointStage h
  rw [← map_sup (T.stage n)]
  exact (T.stage_weighted n).mass_add s t hst

end PositiveMassDenominatorTower

end SuccessorTree.NonPrecompact.BooleanBanana
