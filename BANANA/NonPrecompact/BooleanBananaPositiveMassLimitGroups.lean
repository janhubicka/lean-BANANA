import BANANA.NonPrecompact.BooleanBananaPositiveMassLimitStages
import BANANA.NonPrecompact.BooleanBananaMassStoneDynamics

/-!
# Uniform finite groups on an exhausted positive-mass Boolean algebra

On a chain of uniform powersets, lifting permutations by retaining child
labels extends them to global marked mass-preserving automorphisms.
Their image subgroups form an increasing sequence. Every finite part
of an arbitrary mass-preserving automorphism agrees with one of them.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open scoped Classical
open Set Filter Topology

variable {B : Type} [BooleanAlgebra B] {J : ℕ → Type}
  [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)] [∀ n, Nonempty (J n)]
  {mark : B → ZMod 2} {mass : B → ℝ}

/-- The uniform stages of a Boolean algebra, with their atom labels and
compatible embeddings into the common algebra. Mass is normalised to one. -/
structure UniformMassTower (J : ℕ → Type)
    [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)]
    (mark : B → ZMod 2) (mass : B → ℝ) where
  children : ℕ → ℕ
  split : ∀ n, J (n + 1) ≃ J n × Fin (children n)
  stage : ∀ n, BoundedLatticeHom (Finset (J n)) B
  stage_injective : ∀ n, Function.Injective (stage n)
  stage_step : ∀ n s,
    stage (n + 1) (positiveMassAtomPreimage (fun j => (split n j).1) s) = stage n s
  covers : ∀ x : B, ∃ n s, stage n s = x
  mass_stage : ∀ n s, mass (stage n s) = (s.card : ℝ) / (Fintype.card (J n) : ℝ)
  mark_stage : ∀ n s, mark (stage n s) = (s.card : ZMod 2)

namespace UniformMassTower

variable (T : UniformMassTower J mark mass)

private def stepMap (n : ℕ) : BoundedLatticeHom (Finset (J n)) (Finset (J (n + 1))) :=
  positiveMassAtomPreimage (fun j => (T.split n j).1)

private def stepPerm (n : ℕ) : Equiv.Perm (J n) →* Equiv.Perm (J (n + 1)) :=
  (T.split n).symm.permCongrHom.toMonoidHom.comp (uniformAtomPermLift (J n) (T.children n))

private theorem stepPerm_comm (n : ℕ) (π : Equiv.Perm (J n)) (s : Finset (J n)) :
    uniformPowersetOrderIso (T.stepPerm n π) (T.stepMap n s) =
      T.stepMap n (uniformPowersetOrderIso π s) := by
  ext j
  change j ∈ (T.stepMap n s).map (T.stepPerm n π).toEmbedding ↔
    j ∈ T.stepMap n (s.map π.toEmbedding)
  rw [Finset.mem_map_equiv]
  have h : (T.split n ((T.stepPerm n π).symm j)).1 = π.symm (T.split n j).1 := by
    change (T.split n ((T.split n).symm (((uniformAtomPermLift (J n)
      (T.children n)) π).symm (T.split n j)))).1 = _
    rw [(T.split n).apply_symm_apply]
    rfl
  simp [stepMap, positiveMassAtomPreimage, h, Finset.mem_map_equiv]

/-- Include a stage in a later stage. -/
def liftSet {n m : ℕ} (h : n ≤ m) (s : Finset (J n)) : Finset (J m) :=
  Nat.leRecOn h (fun {l} => T.stepMap l) s

/-- Retain child labels from a starting stage throughout the chain. -/
def liftPerm {n m : ℕ} (h : n ≤ m) (π : Equiv.Perm (J n)) : Equiv.Perm (J m) :=
  Nat.leRecOn h (fun {l} => T.stepPerm l) π

private theorem liftSet_self (n : ℕ) (s : Finset (J n)) : T.liftSet (le_refl n) s = s :=
  @Nat.leRecOn_self (fun n => Finset (J n)) n (fun {l} => T.stepMap l) s

private theorem liftSet_succ {n m : ℕ} (h : n ≤ m) (s : Finset (J n)) :
    T.liftSet (Nat.le_succ_of_le h) s = T.stepMap m (T.liftSet h s) :=
  @Nat.leRecOn_succ (fun n => Finset (J n)) n m h _ (fun {l} => T.stepMap l) s

private theorem liftPerm_self (n : ℕ) (π : Equiv.Perm (J n)) : T.liftPerm (le_refl n) π = π :=
  @Nat.leRecOn_self (fun n => Equiv.Perm (J n)) n (fun {l} => T.stepPerm l) π

private theorem liftPerm_succ {n m : ℕ} (h : n ≤ m) (π : Equiv.Perm (J n)) :
    T.liftPerm (Nat.le_succ_of_le h) π = T.stepPerm m (T.liftPerm h π) :=
  @Nat.leRecOn_succ (fun n => Equiv.Perm (J n)) n m h _ (fun {l} => T.stepPerm l) π

private theorem stage_liftSet {n m : ℕ} (h : n ≤ m) (s : Finset (J n)) :
    T.stage m (T.liftSet h s) = T.stage n s := by
  induction h with
  | refl => rw [liftSet_self]
  | step h ih =>
    rw [T.liftSet_succ h, show T.stage _ (T.stepMap _ _) = _ from T.stage_step _ _, ih]

private theorem liftPerm_mul {n m : ℕ} (h : n ≤ m) (π τ : Equiv.Perm (J n)) :
    T.liftPerm h (π * τ) = T.liftPerm h π * T.liftPerm h τ := by
  induction h with
  | refl => simp only [liftPerm_self]
  | step h ih => simp only [T.liftPerm_succ h, ih, map_mul]

private theorem liftPerm_one {n m : ℕ} (h : n ≤ m) :
    T.liftPerm h (1 : Equiv.Perm (J n)) = 1 := by
  induction h with
  | refl => simp only [liftPerm_self]
  | step h ih => simp only [T.liftPerm_succ h, ih, map_one]

private theorem liftPerm_trans {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l)
    (π : Equiv.Perm (J n)) :
    T.liftPerm (hnm.trans hml) π = T.liftPerm hml (T.liftPerm hnm π) :=
  @Nat.leRecOn_trans (fun n => Equiv.Perm (J n)) n m l hnm hml (fun {l} => T.stepPerm l) π

private theorem stage_liftPerm_liftSet {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l)
    (π : Equiv.Perm (J n)) (s : Finset (J m)) :
    T.stage l (uniformPowersetOrderIso (T.liftPerm (hnm.trans hml) π)
      (T.liftSet hml s)) =
    T.stage m (uniformPowersetOrderIso (T.liftPerm hnm π) s) := by
  induction hml with
  | refl => rw [liftSet_self]
  | step h ih =>
    rw [show T.liftPerm (hnm.trans (Nat.le_succ_of_le h)) π =
        T.stepPerm _ (T.liftPerm (hnm.trans h) π) from T.liftPerm_succ _ _,
      T.liftSet_succ h, stepPerm_comm, show T.stage _ (T.stepMap _ _) = _ from T.stage_step _ _, ih]

private theorem exists_stageAbove (n : ℕ) (x : B) : ∃ m, n ≤ m ∧ ∃ s, T.stage m s = x := by
  obtain ⟨l, s, rfl⟩ := T.covers x
  exact ⟨max n l, le_max_left _ _, T.liftSet (le_max_right n l) s, T.stage_liftSet _ _⟩

private theorem exists_stageCoveringFiniteAbove (n : ℕ) (F : Finset B) :
    ∃ m, n ≤ m ∧ ∀ x ∈ F, ∃ s, T.stage m s = x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨n, le_refl _, by simp⟩
  | @insert x F _ ih =>
    obtain ⟨m, hm, hF⟩ := ih
    obtain ⟨l, hl, s, hs⟩ := T.exists_stageAbove m x
    refine ⟨l, hm.trans hl, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact ⟨s, hs⟩
    · obtain ⟨t, ht⟩ := hF y hy'
      exact ⟨T.liftSet hl t, (T.stage_liftSet hl t).trans ht⟩

private theorem perm_image_agrees {n m l : ℕ} (hnm : n ≤ m) (hnl : n ≤ l)
    (π : Equiv.Perm (J n)) (s : Finset (J m)) (t : Finset (J l))
    (h : T.stage m s = T.stage l t) :
    T.stage m (uniformPowersetOrderIso (T.liftPerm hnm π) s) =
      T.stage l (uniformPowersetOrderIso (T.liftPerm hnl π) t) := by
  have hst : T.liftSet (le_max_left m l) s = T.liftSet (le_max_right m l) t :=
    T.stage_injective _ ((T.stage_liftSet _ _).trans (h.trans (T.stage_liftSet _ _).symm))
  rw [← T.stage_liftPerm_liftSet hnm (le_max_left m l) π s,
    ← T.stage_liftPerm_liftSet hnl (le_max_right m l) π t, hst]

private noncomputable def evalPerm (n : ℕ) (π : Equiv.Perm (J n)) (x : B) : B :=
  let h := T.exists_stageAbove n x
  T.stage h.choose (uniformPowersetOrderIso (T.liftPerm h.choose_spec.1 π)
    (h.choose_spec.2.choose))

private theorem evalPerm_stage {n m : ℕ} (h : n ≤ m) (π : Equiv.Perm (J n)) (s : Finset (J m)) :
    T.evalPerm n π (T.stage m s) =
      T.stage m (uniformPowersetOrderIso (T.liftPerm h π) s) := by
  unfold evalPerm
  dsimp only
  exact T.perm_image_agrees _ h π _ _ (T.exists_stageAbove n (T.stage m s)).choose_spec.2.choose_spec

private theorem evalPerm_one (n : ℕ) (x : B) : T.evalPerm n (1 : Equiv.Perm (J n)) x = x := by
  obtain ⟨m, hm, s, rfl⟩ := T.exists_stageAbove n x
  rw [T.evalPerm_stage hm, T.liftPerm_one hm]
  apply congrArg (T.stage m)
  ext j
  change j ∈ s.map (1 : Equiv.Perm (J m)).toEmbedding ↔ j ∈ s
  rw [Finset.mem_map_equiv]
  rfl

private theorem evalPerm_mul (n : ℕ) (π τ : Equiv.Perm (J n)) (x : B) :
    T.evalPerm n (π * τ) x = T.evalPerm n π (T.evalPerm n τ x) := by
  obtain ⟨m, hm, s, rfl⟩ := T.exists_stageAbove n x
  rw [T.evalPerm_stage hm, T.evalPerm_stage hm, T.evalPerm_stage hm, liftPerm_mul]
  apply congrArg (T.stage m)
  ext j
  change j ∈ s.map (T.liftPerm hm π * T.liftPerm hm τ).toEmbedding ↔
    j ∈ (s.map (T.liftPerm hm τ).toEmbedding).map (T.liftPerm hm π).toEmbedding
  simp only [Finset.mem_map_equiv]
  rfl

private theorem evalPerm_le_iff (n : ℕ) (π : Equiv.Perm (J n)) (x y : B) :
    T.evalPerm n π x ≤ T.evalPerm n π y ↔ x ≤ y := by
  obtain ⟨m, hm, hF⟩ := T.exists_stageCoveringFiniteAbove n {x,y}
  obtain ⟨s, rfl⟩ := hF x (by simp)
  obtain ⟨t, rfl⟩ := hF y (by simp)
  have hle (u v : Finset (J m)) : T.stage m u ≤ T.stage m v ↔ u ≤ v := by
    have hs : T.stage m (u ⊔ v) = T.stage m u ⊔ T.stage m v :=
      map_sup (T.stage m) u v
    constructor
    · intro h
      apply sup_eq_right.mp
      apply T.stage_injective m
      rw [hs, sup_eq_right.mpr h]
    · intro h
      apply sup_eq_right.mp
      rw [← hs, sup_eq_right.mpr h]
  rw [T.evalPerm_stage hm, T.evalPerm_stage hm, hle, hle, OrderIso.le_iff_le]

/-- Each atom permutation extends to an actual order automorphism of the
whole Boolean algebra. -/
noncomputable def orderAut (n : ℕ) (π : Equiv.Perm (J n)) : B ≃o B where
  toFun := T.evalPerm n π
  invFun := T.evalPerm n π⁻¹
  left_inv x := by rw [← T.evalPerm_mul, inv_mul_cancel, T.evalPerm_one]
  right_inv x := by rw [← T.evalPerm_mul, mul_inv_cancel, T.evalPerm_one]
  map_rel_iff' {x y} := T.evalPerm_le_iff n π x y

/-- The induced automorphism acts by the prescribed permutation on its
starting powerset stage. -/
theorem orderAut_stage (n : ℕ) (π : Equiv.Perm (J n)) (s : Finset (J n)) :
    T.orderAut n π (T.stage n s) = T.stage n (uniformPowersetOrderIso π s) := by
  change T.evalPerm n π (T.stage n s) = _
  rw [T.evalPerm_stage (le_refl n), liftPerm_self]

/-- The lifted permutations preserve the actual marking and mass and
form a homomorphism into the mass-preserving group. -/
noncomputable def automorphismHom (n : ℕ) : Equiv.Perm (J n) →* massSubgroup mark mass where
  toFun π := ⟨ofMarkedOrderIso (T.orderAut n π) (by
    intro x
    obtain ⟨m, hm, s, rfl⟩ := T.exists_stageAbove n x
    change mark (T.evalPerm n π (T.stage m s)) = _
    rw [T.evalPerm_stage hm, T.mark_stage, T.mark_stage, uniformPowersetOrderIso_card]), by
      intro x
      obtain ⟨m, hm, s, rfl⟩ := T.exists_stageAbove n x
      change mass (T.evalPerm n π (T.stage m s)) = _
      rw [T.evalPerm_stage hm, T.mass_stage, T.mass_stage, uniformPowersetOrderIso_card]⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    exact T.evalPerm_one n x
  map_mul' π τ := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    exact T.evalPerm_mul n π τ x

/-- Passing to a later stage and retaining child labels gives the same
global automorphism. -/
theorem automorphismHom_lift {n m : ℕ} (hm : n ≤ m) (π : Equiv.Perm (J n)) :
    T.automorphismHom m (T.liftPerm hm π) = T.automorphismHom n π := by
  apply Subtype.ext
  apply Subtype.ext
  ext x
  obtain ⟨l, hl, s, rfl⟩ := T.exists_stageAbove m x
  change T.evalPerm m _ (T.stage l s) = T.evalPerm n π (T.stage l s)
  rw [T.evalPerm_stage hl, T.evalPerm_stage (hm.trans hl), T.liftPerm_trans hm hl π]

/-- Every stage gives a finite subgroup of the actual mass subgroup, and
these form an increasing sequence. -/
noncomputable def finiteStage (n : ℕ) : Subgroup (massSubgroup mark mass) :=
  (T.automorphismHom n).range

theorem finite_finiteStage (n : ℕ) : Finite (T.finiteStage n) :=
  Finite.of_surjective (fun π => (⟨T.automorphismHom n π, ⟨π, rfl⟩⟩ : T.finiteStage n))
    (by rintro ⟨g, π, rfl⟩; exact ⟨π, rfl⟩)

theorem finiteStage_mono : Monotone T.finiteStage := by
  intro n m h g hg
  obtain ⟨π, rfl⟩ := hg
  exact ⟨T.liftPerm h π, T.automorphismHom_lift h π⟩

/-- The lifted action faithfully represents the full symmetric group of
each stage. -/
theorem automorphismHom_injective (n : ℕ) : Function.Injective (T.automorphismHom n) := by
  intro π τ h
  ext i
  have he := congrArg (fun g : massSubgroup mark mass => g.val.val (T.stage n {i})) h
  change T.orderAut n π (T.stage n {i}) = T.orderAut n τ (T.stage n {i}) at he
  rw [T.orderAut_stage, T.orderAut_stage] at he
  have ht := T.stage_injective n he
  change (({i} : Finset (J n)).map π.toEmbedding) = ({i} : Finset (J n)).map τ.toEmbedding at ht
  simpa using ht

include T in
/-- The actual finite stages supply the uniform mass cover used to
force invariant clopen probabilities. -/
theorem uniformMassCover : UniformMassCover mark mass := by
  intro b
  obtain ⟨n, s, rfl⟩ := T.covers b
  let d := Fintype.card (J n)
  have hd : 0 < d := Fintype.card_pos
  let e := Fintype.equivFin (J n)
  let p := positiveMassAtomPreimage (e : J n → Fin d)
  let f := (T.stage n).comp p
  let t := s.map e.toEmbedding
  have hp (v : Finset (Fin d)) : p v = v.map e.symm.toEmbedding := by
    ext j
    simp [p, positiveMassAtomPreimage, Finset.mem_map_equiv]
  have hpt : p t = s := by
    ext j
    simp [p, t, positiveMassAtomPreimage, Finset.mem_map_equiv]
  refine ⟨d, hd, f, t, ?_, ?_, ?_⟩
  · change T.stage n (p t) = _
    rw [hpt]
  · rw [T.mass_stage, Finset.card_map]
  · intro i j
    let π := Equiv.swap (e.symm i) (e.symm j)
    refine ⟨T.automorphismHom n π, ?_⟩
    change T.orderAut n π (T.stage n (p {i})) = T.stage n (p {j})
    rw [hp, hp, Finset.map_singleton, Finset.map_singleton, T.orderAut_stage]
    apply congrArg (T.stage n)
    change ({e.symm i} : Finset (J n)).map π.toEmbedding = {e.symm j}
    simp [π]

theorem factor_toStage {A : Type} [BooleanAlgebra A] {n : ℕ}
    (f : BoundedLatticeHom A B) (hf : Function.Injective f)
    (h : ∀ a, ∃ s, T.stage n s = f a) :
    ∃ g : BoundedLatticeHom A (Finset (J n)), Function.Injective g ∧
      ∀ a, T.stage n (g a) = f a := by
  choose q hq using h
  let g : BoundedLatticeHom A (Finset (J n)) :=
    { toFun := q
      map_bot' := T.stage_injective n (by rw [hq, map_bot f, map_bot (T.stage n)])
      map_top' := T.stage_injective n (by rw [hq, TopHomClass.map_top f, TopHomClass.map_top (T.stage n)])
      map_sup' a b := T.stage_injective n (by
        change T.stage n (q (a ⊔ b)) = T.stage n (q a ⊔ q b)
        rw [hq, map_sup (T.stage n), hq, hq, map_sup f])
      map_inf' a b := T.stage_injective n (by
        change T.stage n (q (a ⊓ b)) = T.stage n (q a ⊓ q b)
        rw [hq, map_inf (T.stage n), hq, hq, map_inf f]) }
  refine ⟨g, ?_, hq⟩
  intro a b h
  apply hf
  exact (hq a).symm.trans ((congrArg (T.stage n) h).trans (hq b))

/-- Every prescribed finite part of any actual mass-preserving
automorphism is matched by one of the lifted stage permutations. -/
theorem finiteStage_pointwise_approximates (g : massSubgroup mark mass) (F : Finset B) :
    ∃ n, ∃ h : T.finiteStage n, ∀ x ∈ F, h.val.val.val x = g.val.val x := by
  classical
  obtain ⟨n, _, hn⟩ := T.exists_stageCoveringFiniteAbove 0 F
  let q : BoundedLatticeHom (Finset (J n)) B := (g.val.val : BoundedLatticeHom B B).comp (T.stage n)
  let U : Finset B := Finset.univ.image (T.stage n) ∪ Finset.univ.image q
  obtain ⟨m, hmn, hm⟩ := T.exists_stageCoveringFiniteAbove n U
  obtain ⟨u, hu, hu'⟩ := T.factor_toStage (T.stage n) (T.stage_injective n)
    (fun s => hm _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ s))))
  obtain ⟨v, hv, hv'⟩ := T.factor_toStage q (g.val.val.injective.comp (T.stage_injective n))
    (fun s => hm _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ s))))
  have hsize (s : Finset (J n)) : (u s).card = (v s).card := by
    have hs := (T.mass_stage m (u s)).symm.trans
      ((congrArg mass (hu' s)).trans ((g.property (T.stage n s)).symm.trans
        ((congrArg mass (hv' s)).symm.trans (T.mass_stage m (v s)))))
    have hD : (Fintype.card (J m) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (J m) ≠ 0)
    exact_mod_cast (div_left_inj' hD).mp hs
  obtain ⟨π, hπ⟩ := exists_uniformStage_permutation u v hu hv hsize
  refine ⟨m, ⟨T.automorphismHom m π, ⟨π, rfl⟩⟩, fun x hx => ?_⟩
  obtain ⟨s, rfl⟩ := hn x hx
  change T.orderAut m π (T.stage n s) = g.val.val (T.stage n s)
  rw [← hu' s, T.orderAut_stage, hπ, hv', hu' s]
  rfl

/-- The increasing union of the finite stages is dense in the actual
pointwise topology of the marked mass-preserving group. -/
theorem finiteStage_dense : Dense (⋃ n, (T.finiteStage n : Set (massSubgroup mark mass))) := by
  classical
  intro g
  rw [mem_closure_iff_nhds]
  intro U hU
  let eval (g : massSubgroup mark mass) : B → WithDiscreteTopology B :=
    fun x => WithTopology.toTopology ⊥ (g.val.val x)
  change U ∈ @nhds _ (TopologicalSpace.induced (Subtype.val : massSubgroup mark mass →
    markedAutomorphisms mark) (TopologicalSpace.induced
      (fun g : markedAutomorphisms mark => fun x : B => WithTopology.toTopology ⊥ (g.val x))
      inferInstance)) g at hU
  rw [induced_compose] at hU
  change U ∈ @nhds _ (TopologicalSpace.induced eval inferInstance) g at hU
  rw [nhds_induced, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, W, hW, hWV⟩ := hV
  obtain ⟨n, h, htest⟩ := T.finiteStage_pointwise_approximates g I
  refine ⟨h.val, hVU (hWV ?_), Set.mem_iUnion.mpr ⟨n, h.property⟩⟩
  intro i hi
  change WithTopology.toTopology ⊥ (h.val.val.val i) ∈ W i
  rw [htest i hi]
  exact mem_of_mem_nhds (hW i)

include T in
/-- The dense increasing union gives amenability of the mass subgroup. -/
theorem massSubgroup_amenable : IsTopologicallyAmenable (massSubgroup mark mass) :=
  isTopologicallyAmenable_of_dense_finite_subgroups T.finiteStage
    (fun i j => ⟨max i j, T.finiteStage_mono (le_max_left _ _), T.finiteStage_mono (le_max_right _ _)⟩)
    T.finite_finiteStage T.finiteStage_dense

end UniformMassTower

end SuccessorTree.NonPrecompact.BooleanBanana
