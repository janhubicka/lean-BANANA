import BANANA.NonPrecompact.BananaLimitFirstOrderAutomorphism
import Mathlib.ModelTheory.Fraisse

/-!
# Bounded relational arity cannot present the native BANANA group homogeneously

A binary circuit and an independent tuple match on every proper subset of their
coordinates. Their distinct global orbits contradict homogeneity in bounded arity.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder Language.Structure
open scoped FirstOrder

/-- If two injective finite tuples match on the image of each bounded-arity
tuple, the map on their entries is an embedding of the induced structures. -/
private theorem extend_of_matches_on_small_tuples
    {L : Language} {M : Type*} [L.Structure M] [L.IsRelational]
    {m n : ℕ} (a b : Fin m → M) (ha : Function.Injective a) (hb : Function.Injective b)
    (hbound : ∀ k, Nonempty (L.Relations k) → k ≤ n)
    (hmatches : ∀ k ≤ n, ∀ q : Fin k → Fin m, ∃ g : M ≃[L] M,
      ∀ j, g (a (q j)) = b (q j))
    (hhom : L.IsUltrahomogeneous M) :
    ∃ g : M ≃[L] M, ∀ i, g (a i) = b i := by
  classical
  let S : L.Substructure M := {
    carrier := Set.range a
    fun_mem := fun f _ _ => isEmptyElim f }
  let e : Fin m ≃ S :=
    Equiv.ofBijective (fun i => (⟨a i, ⟨i, rfl⟩⟩ : S))
      ⟨fun _ _ h => ha (congrArg Subtype.val h), by
        rintro ⟨x, i, rfl⟩
        exact ⟨i, rfl⟩⟩
  have he (i : Fin m) : (e i : M) = a i := rfl
  let f : S ↪[L] M := {
    toFun := b ∘ e.symm
    inj' := hb.comp e.symm.injective
    map_fun' := fun t _ => isEmptyElim t
    map_rel' := by
      intro k r t
      let q : Fin k → Fin m := e.symm ∘ t
      obtain ⟨g, hg⟩ := hmatches k (hbound k ⟨r⟩) q
      have ht (i : Fin k) : a (q i) = (t i : M) := by
        change a (e.symm (t i)) = _
        rw [← he, e.apply_symm_apply]
      have hEq : (b ∘ e.symm) ∘ t = g ∘ (Subtype.val ∘ t) := by
        funext i
        exact (hg i).symm.trans (congrArg g (ht i))
      change RelMap r ((b ∘ e.symm) ∘ t) ↔
        RelMap r (Subtype.val ∘ t)
      rw [hEq, g.map_rel] }
  have : Finite S := Finite.of_equiv (Fin m) e
  obtain ⟨g, hg⟩ := hhom S Language.Substructure.FG.of_finite f
  refine ⟨g, fun i => ?_⟩
  have h := congrArg (fun h : S ↪[L] M => h (e i)) hg
  change b (e.symm (e i)) = g (a i) at h
  simpa using h.symm


private def coordinate {m : ℕ} (i : Fin m) : ℚ := i.val

private theorem coordinate_injective (m : ℕ) :
    Function.Injective (@coordinate m) := by
  intro i j h
  apply Fin.ext
  change ((i.val : ℕ) : ℚ) = ((j.val : ℕ) : ℚ) at h
  exact_mod_cast h

private noncomputable def axis {m : ℕ} (i : Fin m) : BananaLimitVector :=
  Finsupp.single (coordinate i) 1

private theorem axis_apply {m : ℕ} (i j : Fin m) : axis i (coordinate j) = if i = j then 1 else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp [axis]
  · have h' : coordinate i ≠ coordinate j := (coordinate_injective _).ne h
    simp [axis, h, h'.symm]

private theorem axis_sum_apply {m : ℕ} (c : Fin m → F2) (j : Fin m) :
    (∑ i, c i • axis i) (coordinate j) = c j := by
  classical
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul, axis_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ h
    simp [h]
  · simp

private theorem axis_linearIndependent (m : ℕ) :
    LinearIndependent F2 (@axis m) := by
  refine Fintype.linearIndependent_iff.2 fun c h i => ?_
  have h' := congrArg (fun x : BananaLimitVector => x (coordinate i)) h
  rw [axis_sum_apply, Finsupp.zero_apply] at h'
  exact h'

private noncomputable def circuit (m : ℕ) : Fin (m + 1) → BananaLimitVector :=
  Fin.snoc axis (∑ i : Fin m, axis i)

private theorem circuit_sum_apply {m : ℕ} (c : Fin (m + 1) → F2) (j : Fin m) :
    (∑ i, c i • circuit m i) (coordinate j) = c j.castSucc + c (Fin.last m) := by
  classical
  rw [Fin.sum_univ_castSucc]
  simp only [circuit, Fin.snoc_castSucc, Fin.snoc_last, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, axis_sum_apply]
  have h : (∑ i : Fin m, axis i) (coordinate j) = 1 := by
    simpa only [one_smul] using axis_sum_apply (fun _ : Fin m => (1 : F2)) j
  rw [h, mul_one]

private theorem circuit_indepOn {m : ℕ} (s : Finset (Fin (m + 1))) (hs : s ≠ Finset.univ) :
    LinearIndepOn F2 (circuit m) s := by
  classical
  rw [linearIndepOn_finset_iff]
  intro c hsum
  let d (i : Fin (m + 1)) : F2 := if i ∈ s then c i else 0
  have hd : ∑ i, d i • circuit m i = 0 := by
    rw [← hsum]
    simp only [d, ite_smul, zero_smul, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have eq (j : Fin m) : d j.castSucc + d (Fin.last m) = 0 := by
    have h := congrArg (fun x : BananaLimitVector => x (coordinate j)) hd
    rw [circuit_sum_apply, Finsupp.zero_apply] at h
    exact h
  obtain ⟨i, hi⟩ : ∃ i, i ∉ s := by
    by_contra! h
    exact hs (Finset.eq_univ_of_forall h)
  have hdi : d i = 0 := ite_eq_right hi
  have hl : d (Fin.last m) = 0 := by
    cases i using Fin.lastCases with
    | last => exact hdi
    | cast j => simpa only [hdi, zero_add] using eq j
  intro i hi
  have hdi : d i = 0 := by
    cases i using Fin.lastCases with
    | last => exact hl
    | cast j => simpa only [hl, add_zero] using eq j
  simpa only [d, ite_eq_left hi] using hdi

private theorem circuit_not_independent (m : ℕ) :
    ¬LinearIndependent F2 (circuit m) := by
  intro h
  have hcomb : ∑ i : Fin (m + 1), (1 : F2) • circuit m i = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [circuit, Fin.snoc_castSucc, Fin.snoc_last, one_smul]
    exact ZModModule.add_self _
  exact one_ne_zero (Fintype.linearIndependent_iff.mp h _ hcomb (Fin.last m))


private theorem circuit_injective {m : ℕ} (hm : 2 ≤ m) :
    Function.Injective (circuit m) := by
  classical
  intro i j h
  by_contra hij
  let s : Finset (Fin (m + 1)) := {i, j}
  have hs : s ≠ Finset.univ := by
    intro hu
    have hc : s.card = m + 1 := by simp [hu]
    have hd : s.card = 2 := by simp [s, hij]
    omega
  have hi : i ∈ s := by simp [s]
  have hj : j ∈ s := by simp [s]
  exact hij (congrArg Subtype.val ((circuit_indepOn s hs).injective
    (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) h))

private theorem independent_left_tuples_same_orbit {k : ℕ} (a b : Fin k → BananaLimitVector)
    (ha : LinearIndependent F2 a) (hb : LinearIndependent F2 b) :
    ∃ g : BananaLimitAutomorphism, ∀ i, g • (Sum.inl (a i) : BananaTaggedCarrier) = Sum.inl (b i) := by
  let z : Fin 0 → BananaLimitVector := Fin.elim0
  have comb_eq_zero (v : Fin k → BananaLimitVector) (hv : LinearIndependent F2 v)
      (c : Fin k → F2) : bananaLimitTupleCombination v c = 0 ↔ c = 0 := by
    constructor
    · intro h
      exact funext (Fintype.linearIndependent_iff.mp hv c
        (by simpa [bananaLimitTupleCombination, Fintype.linearCombination_apply] using h))
    · rintro rfl
      exact map_zero _
  have hs : bananaLimitTupleSignature a z = bananaLimitTupleSignature b z := by
    classical
    apply Prod.ext
    · funext c
      simp only [bananaLimitTupleSignature, comb_eq_zero a ha, comb_eq_zero b hb]
    · apply Prod.ext
      · rfl
      · funext i j
        exact Fin.elim0 j
  obtain ⟨EL, ER, hpair, hmatch, -⟩ := bananaLimitTupleSignature_complete a b z z hs
  exact ⟨⟨(EL, ER), hpair⟩, fun i => congrArg Sum.inl (hmatch i)⟩

/-- No bounded-arity relational structure on the native BANANA carrier can
simultaneously be homogeneous and have exactly the native point action. The
hypotheses say the two automorphism groups induce the same permutations. -/
theorem banana_not_ultrahomogeneous_of_bounded_relations
    {L : Language} [L.Structure BananaTaggedCarrier] [L.IsRelational]
    (n : ℕ) (hbound : ∀ k, Nonempty (L.Relations k) → k ≤ n)
    (toRel : ∀ g : BananaLimitAutomorphism, ∃ h : BananaTaggedCarrier ≃[L] BananaTaggedCarrier,
      ∀ a, h a = g • a)
    (toNative : ∀ h : BananaTaggedCarrier ≃[L] BananaTaggedCarrier, ∃ g : BananaLimitAutomorphism,
      ∀ a, g • a = h a) :
    ¬ L.IsUltrahomogeneous BananaTaggedCarrier := by
  classical
  intro hhom
  let m := n + 2
  let a : Fin (m + 1) → BananaTaggedCarrier := Sum.inl ∘ circuit m
  let b : Fin (m + 1) → BananaTaggedCarrier := Sum.inl ∘ axis
  have ha : Function.Injective a := Sum.inl_injective.comp (circuit_injective (by omega))
  have hb : Function.Injective b := Sum.inl_injective.comp (axis_linearIndependent _).injective
  have hmatches (k : ℕ) (hk : k ≤ n) (q : Fin k → Fin (m + 1)) :
      ∃ g : BananaTaggedCarrier ≃[L] BananaTaggedCarrier, ∀ j, g (a (q j)) = b (q j) := by
    let s : Finset (Fin (m + 1)) := Finset.univ.image q
    have hcard : s.card ≤ n := by
      exact (Finset.card_image_le.trans_eq (Finset.card_univ.trans (Fintype.card_fin k))).trans hk
    have hs : s ≠ Finset.univ := by
      intro h
      rw [h, Finset.card_univ, Fintype.card_fin] at hcard
      omega
    let e : s ≃ Fin s.card := s.equivFin
    let f : Fin s.card → Fin (m + 1) := Subtype.val ∘ e.symm
    have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
    have hca : LinearIndependent F2 (circuit m ∘ f) :=
      (circuit_indepOn s hs).comp e.symm e.symm.injective
    have hcb : LinearIndependent F2 (axis ∘ f) := (axis_linearIndependent _).comp f hf
    obtain ⟨g, hg⟩ := independent_left_tuples_same_orbit _ _ hca hcb
    obtain ⟨g', hg'⟩ := toRel g
    refine ⟨g', fun j => ?_⟩
    let i : s := ⟨q j, Finset.mem_image_of_mem q (Finset.mem_univ j)⟩
    have hfq : f (e i) = q j := by simp [f, i]
    simpa only [a, b, Function.comp_apply, hg', ← hfq] using hg (e i)
  obtain ⟨h, hh⟩ := extend_of_matches_on_small_tuples a b ha hb hbound hmatches hhom
  obtain ⟨g, hg⟩ := toNative h
  have hmap : g.val.1 ∘ circuit m = axis := by
    funext i
    exact Sum.inl.inj ((hg (a i)).trans (hh i))
  apply circuit_not_independent m
  apply LinearIndependent.of_comp g.val.1.toLinearMap
  exact hmap ▸ axis_linearIndependent _


/-- In particular a finite relational signature on the same carrier cannot make
the native BANANA permutation group homogeneous. -/
theorem banana_not_ultrahomogeneous_of_finite_relations
    {L : Language} [L.Structure BananaTaggedCarrier] [L.IsRelational]
    [Finite (Σ k, L.Relations k)]
    (toRel : ∀ g : BananaLimitAutomorphism, ∃ h : BananaTaggedCarrier ≃[L] BananaTaggedCarrier,
      ∀ a, h a = g • a)
    (toNative : ∀ h : BananaTaggedCarrier ≃[L] BananaTaggedCarrier, ∃ g : BananaLimitAutomorphism,
      ∀ a, g • a = h a) :
    ¬ L.IsUltrahomogeneous BananaTaggedCarrier := by
  let arity : (Σ k, L.Relations k) → ℕ := Sigma.fst
  obtain ⟨n, hn⟩ := (Set.finite_range arity).bddAbove
  apply banana_not_ultrahomogeneous_of_bounded_relations n _ toRel toNative
  rintro k ⟨r⟩
  exact hn ⟨⟨k, r⟩, rfl⟩

/-- The concrete relational presentation with addition graphs and zero tags
has the native group but fails ultrahomogeneity for induced substructures. -/
theorem bananaTagged_not_ultrahomogeneous :
    ¬ bananaTaggedLanguage.IsUltrahomogeneous BananaTaggedCarrier := by
  let : bananaTaggedLanguage.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)
  refine banana_not_ultrahomogeneous_of_bounded_relations 3 ?_ ?_ ?_
  · rintro k ⟨r⟩
    cases r <;> decide
  · intro g
    exact ⟨(bananaLimit_firstOrderAut g).toEquiv, bananaLimit_firstOrderAut_apply g⟩
  · intro g
    exact ⟨bananaLimit_nativeAut (FirstOrderAut.ofEquiv g),
      bananaLimit_nativeAut_smul (FirstOrderAut.ofEquiv g)⟩

end SuccessorTree.NonPrecompact
