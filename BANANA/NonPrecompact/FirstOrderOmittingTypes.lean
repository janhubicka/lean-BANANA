import BANANA.NonPrecompact.FirstOrderCountablyCategoricalTypes
import Mathlib.ModelTheory.Encoding

/-!
# Omitting a non-isolated complete type in a countable language

The Baire space of types in countably many fresh names has a dense set
of Henkin witnesses and a dense set of assignments omitting the given
type on each finite named tuple. The resulting named set is elementary
by the Tarski–Vaught test in Mathlib.
-/

open FirstOrder Cardinal
open scoped FirstOrder

namespace SuccessorTree.NonPrecompact

variable {L : Language.{0, 0}} {T : L.Theory}

/-- Isolation of a complete type by a single formula in its free variables. -/
def CompleteTypeIsIsolated {n : ℕ} (p : T.CompleteType (Fin n)) : Prop :=
  ∃ φ : L[[Fin n]].Sentence, T.typesWith φ = {p}

/-- The finite existential projection of a formula onto prescribed names.
The equations also cover assignments of multiple tuple entries to the same name. -/
private noncomputable def projectNamedFormula {n : ℕ}
    (φ : L.Formula ℕ) (s : Fin n → ℕ) : L.Formula (Fin n) :=
  let U := φ.freeVarFinset ∪ Finset.univ.image s
  let ψ : L.Formula (Fin n ⊕ U) :=
    φ.restrictFreeVar fun i => .inr ⟨i, Finset.mem_union_left _ i.property⟩
  let eqs : L.Formula (Fin n ⊕ U) := Language.Formula.iInf fun i : Fin n =>
    (Language.Term.var (.inr ⟨s i, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩)).equal (Language.Term.var (.inl i))
  (ψ ⊓ eqs).iExs U

private theorem realize_projectNamedFormula {n : ℕ} (φ : L.Formula ℕ) (s : Fin n → ℕ)
    {M : Type} [L.Structure M] [Nonempty M] (v : Fin n → M) :
    (projectNamedFormula φ s).Realize v ↔ ∃ a : ℕ → M, φ.Realize a ∧ a ∘ s = v := by
  classical
  let U := φ.freeVarFinset ∪ Finset.univ.image s
  have hs (i : Fin n) : s i ∈ U :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let res : φ.freeVarFinset → U := fun i => ⟨i, Finset.mem_union_left _ i.property⟩
  unfold projectNamedFormula
  simp only [Language.Formula.realize_iExs, Language.Formula.realize_inf,
    Language.Formula.realize_iInf, Language.Formula.realize_equal, Language.Term.realize_var,
    Sum.elim_inr, Sum.elim_inl]
  constructor
  · rintro ⟨w, hw, heq⟩
    let a (i : ℕ) : M := if hi : i ∈ U then w ⟨i, hi⟩ else Classical.choice inferInstance
    have hvar (i : φ.freeVarFinset) : (Sum.elim v w) (.inr (res i)) = a i := by
      have hi : (i : ℕ) ∈ U := (res i).property
      simp [a, res, hi]
    exact ⟨a, (Language.BoundedFormula.realize_restrictFreeVar a hvar).mp hw,
      funext fun i => (dite_eq_left (hs i)).trans (heq i)⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨fun i => a i, ?_, fun _ => rfl⟩
    have hc : Language.Formula.Realize (φ.restrictFreeVar (fun i => Sum.inr (res i)))
        (Sum.elim (a ∘ s) (fun i : U => a i)) ↔ φ.Realize a :=
      Language.BoundedFormula.realize_restrictFreeVar a (fun _ => rfl)
    exact hc.mpr ha

private def omitNamedTuple {n : ℕ} (p : T.CompleteType (Fin n)) (s : Fin n → ℕ) :
    Set (T.CompleteType ℕ) :=
  ⋃ (φ : L.Formula (Fin n)) (_ : Language.Formula.equivSentence φ ∈ p),
    T.typesWith (Language.Formula.equivSentence (φ.not.relabel s))

private theorem isOpen_omitNamedTuple {n : ℕ} (p : T.CompleteType (Fin n)) (s : Fin n → ℕ) :
    IsOpen (omitNamedTuple p s) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => CompleteType.isOpen_typesWith _

private theorem dense_omitNamedTuple {n : ℕ} (p : T.CompleteType (Fin n))
    (hp : ¬ CompleteTypeIsIsolated p) (s : Fin n → ℕ) :
    Dense (omitNamedTuple p s) := by
  classical
  rw [dense_iff_inter_open]
  intro U hU ⟨q, hq⟩
  obtain ⟨_, ⟨σ, rfl⟩, hσq, hσsub⟩ :=
    CompleteType.isTopologicalBasis_range_typesWith.exists_subset_of_mem_open hq hU
  let φ : L.Formula ℕ := Language.Formula.equivSentence.symm σ
  let χ : L.Formula (Fin n) := projectNamedFormula φ s
  let χ' : L[[Fin n]].Sentence := Language.Formula.equivSentence χ
  obtain ⟨M, a, rfl⟩ := T.exists_modelType_is_realized_in q
  have hφ : φ.Realize a := by
    simpa only [Language.Theory.CompleteType.mem_typesWith_iff,
      Language.Theory.CompleteType.mem_typeOf] using hσq
  have hχ : χ' ∈ T.typeOf (a ∘ s) :=
    Language.Theory.CompleteType.formula_mem_typeOf.mpr
      ((realize_projectNamedFormula _ _ _).mpr ⟨a, hφ, rfl⟩)
  have hex : ∃ q' : T.CompleteType (Fin n), χ' ∈ q' ∧ q' ≠ p := by
    by_contra! hall
    apply hp
    refine ⟨χ', ?_⟩
    ext z
    constructor
    · exact fun h => Set.mem_singleton_iff.mpr (hall z h)
    · rintro rfl
      exact (hall _ hχ) ▸ hχ
  obtain ⟨q', hqχ, hq'⟩ := hex
  have hsep : ∃ τ : L[[Fin n]].Sentence, τ ∈ p ∧ τ.not ∈ q' := by
    have hne : ¬ ∀ τ : L[[Fin n]].Sentence, (τ ∈ q' ↔ τ ∈ p) :=
      fun h => hq' (SetLike.ext h)
    obtain ⟨τ, ht⟩ := not_forall.mp hne
    by_cases hmem : τ ∈ p
    · exact ⟨τ, hmem, (q'.not_mem_iff τ).mpr (fun h => ht (iff_of_true h hmem))⟩
    · have hq : τ ∈ q' := by
        by_contra hn
        exact ht (iff_of_false hn hmem)
      exact ⟨τ.not, (p.not_mem_iff τ).mpr hmem,
        (q'.not_mem_iff τ.not).mpr (fun h => (q'.not_mem_iff τ).mp h hq)⟩
  obtain ⟨τ, hpτ, hqτ⟩ := hsep
  obtain ⟨M', v, rfl⟩ := T.exists_modelType_is_realized_in q'
  let ψ : L.Formula (Fin n) := Language.Formula.equivSentence.symm τ
  have hχv : χ.Realize v := Language.Theory.CompleteType.formula_mem_typeOf.mp hqχ
  obtain ⟨a', hσ', has⟩ := (realize_projectNamedFormula _ _ _).mp hχv
  have hψ : ψ.not.Realize v :=
    Language.Theory.CompleteType.formula_mem_typeOf.mp (by
      simpa only [Language.Formula.equivSentence_not, Equiv.apply_symm_apply, ψ] using hqτ)
  refine ⟨T.typeOf a', hσsub ?_, ?_⟩
  · exact Language.Theory.CompleteType.mem_typeOf.mpr hσ'
  · refine Set.mem_iUnion.mpr ⟨ψ, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · simpa only [ψ, Equiv.apply_symm_apply] using hpτ
    · exact Language.Theory.CompleteType.formula_mem_typeOf.mpr
        (by rwa [Language.Formula.realize_relabel, has])

private theorem realize_iff_of_eq_on_freeVars {α : Type} [DecidableEq α]
    {M : Type} [L.Structure M] {φ : L.Formula α} {a b : α → M}
    (h : ∀ i ∈ φ.freeVarFinset, a i = b i) :
    φ.Realize a ↔ φ.Realize b := by
  let v : φ.freeVarFinset → M := fun i => a i
  have ha : Language.Formula.Realize (φ.restrictFreeVar id) v ↔ φ.Realize a :=
    Language.BoundedFormula.realize_restrictFreeVar a (fun _ => rfl)
  have hb : Language.Formula.Realize (φ.restrictFreeVar id) v ↔ φ.Realize b :=
    Language.BoundedFormula.realize_restrictFreeVar b (fun i => h i i.property)
  exact ha.symm.trans hb

private def withNamedWitness (ψ : L.Formula (ℕ ⊕ Unit)) : Set (T.CompleteType ℕ) :=
  T.typesWith (Language.Formula.equivSentence (ψ.iExs Unit).not) ∪
  ⋃ k : ℕ, T.typesWith (Language.Formula.equivSentence (ψ.relabel (Sum.elim id fun _ => k)))

private theorem isOpen_withNamedWitness (ψ : L.Formula (ℕ ⊕ Unit)) :
    IsOpen (withNamedWitness (T := T) ψ) :=
  (CompleteType.isOpen_typesWith _).union (isOpen_iUnion fun _ => CompleteType.isOpen_typesWith _)

private theorem dense_withNamedWitness (ψ : L.Formula (ℕ ⊕ Unit)) :
    Dense (withNamedWitness (T := T) ψ) := by
  classical
  rw [dense_iff_inter_open]
  intro U hU ⟨q, hq⟩
  obtain ⟨_, ⟨σ, rfl⟩, hσq, hσsub⟩ :=
    CompleteType.isTopologicalBasis_range_typesWith.exists_subset_of_mem_open hq hU
  let φ : L.Formula ℕ := Language.Formula.equivSentence.symm σ
  obtain ⟨M, a, rfl⟩ := T.exists_modelType_is_realized_in q
  have hφ : φ.Realize a := Language.Theory.CompleteType.mem_typeOf.mp hσq
  by_cases hψ : (ψ.iExs Unit).Realize a
  · obtain ⟨w, hw⟩ := Language.Formula.realize_iExs.mp hψ
    obtain ⟨k, hk⟩ := Infinite.exists_notMem_finset
      (φ.freeVarFinset ∪ ψ.freeVarFinset.image (Sum.elim id fun _ => 0))
    let b := Function.update a k (w ())
    have hl (i : ℕ) (hi : i ∈ φ.freeVarFinset) : a i = b i := by
      have hik : i ≠ k := by rintro rfl; exact hk (Finset.mem_union_left _ hi)
      simp [b, Function.update_of_ne hik]
    have hr (i : ℕ ⊕ Unit) (hi : i ∈ ψ.freeVarFinset) :
        Sum.elim a w i = Sum.elim b (fun _ => b k) i := by
      cases i with
      | inl i =>
        have hik : i ≠ k := by
          rintro rfl
          exact hk (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨Sum.inl i, hi, rfl⟩))
        simp [b, Function.update_of_ne hik]
      | inr i =>
        cases i
        simp [b]
    have hφb := (realize_iff_of_eq_on_freeVars hl).mp hφ
    have hψb := (realize_iff_of_eq_on_freeVars hr).mp hw
    refine ⟨T.typeOf b, hσsub (Language.Theory.CompleteType.mem_typeOf.mpr hφb), Or.inr ?_⟩
    refine Set.mem_iUnion.mpr ⟨k, Language.Theory.CompleteType.formula_mem_typeOf.mpr ?_⟩
    rw [Language.Formula.realize_relabel]
    have heq : b ∘ (Sum.elim id fun _ : Unit => k) = Sum.elim b (fun _ => b k) :=
      funext fun i => by cases i <;> rfl
    rwa [heq]
  · exact ⟨T.typeOf a, hσsub hσq,
      Or.inl (Language.Theory.CompleteType.formula_mem_typeOf.mpr
        (Language.Formula.realize_not.mpr hψ))⟩

private theorem range_meetsDefinable {M : Type} [L.Structure M] [Nonempty M] [M ⊨ T]
    (a : ℕ → M)
    (h : ∀ ψ : L.Formula (ℕ ⊕ Unit), T.typeOf a ∈ withNamedWitness (T := T) ψ) :
    L.MeetsDefinable (Set.range a) := by
  classical
  intro D hx hd
  obtain ⟨x, hx⟩ := hx
  obtain ⟨φ, hφ⟩ := hd
  let name : Set.range a → ℕ := fun b => b.property.choose
  have name_ok (b : Set.range a) : a (name b) = b := b.property.choose_spec
  let ψ : L.Formula (ℕ ⊕ Unit) :=
    Language.Formula.relabel (Sum.elim (.inl ∘ name) fun _ => .inr ())
      (Language.BoundedFormula.constantsVarsEquiv φ)
  have hconv (z : M) :
      ψ.Realize (Sum.elim a (fun _ => z)) ↔ z ∈ D := by
    have he :
        Sum.elim a (fun _ : Unit => z) ∘
          (Sum.elim (.inl ∘ name) fun _ : Fin 1 => .inr ()) =
        Sum.elim (fun b : Set.range a => (L.con b : M)) ![z] := by
      funext i
      cases i with
      | inl b => exact name_ok b
      | inr j => exact Subsingleton.elim j 0 ▸ rfl
    dsimp only [ψ]
    rw [Language.Formula.realize_relabel, he]
    refine (Language.BoundedFormula.realize_constantsVarsEquiv (φ := φ)).trans ?_
    have hh := Set.ext_iff.mp hφ (![z] : Fin 1 → M)
    simpa only [Set.mem_ofPred_eq, Language.Formula.Realize, Fin.isValue, Matrix.cons_val_zero] using hh.symm
  have hψ : (ψ.iExs Unit).Realize a :=
    Language.Formula.realize_iExs.mpr ⟨fun _ => x, (hconv _).mpr hx⟩
  have hh := h ψ
  change _ ∈ _ ∪ _ at hh
  rcases hh with hn | hh
  · exact (Language.Formula.realize_not.mp
      (Language.Theory.CompleteType.formula_mem_typeOf.mp hn) hψ).elim
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hh
    have ht := Language.Theory.CompleteType.formula_mem_typeOf.mp hk
    rw [Language.Formula.realize_relabel] at ht
    have heq : a ∘ (Sum.elim id fun _ : Unit => k) = Sum.elim a (fun _ => a k) :=
      funext fun i => by cases i <;> rfl
    rw [heq] at ht
    exact ⟨a k, (hconv _).mp ht, Set.mem_range_self k⟩

/-- A non-isolated complete finite type in a countable language is omitted by
some countable model of the theory. -/
theorem exists_countable_model_omits_completeType [Countable L.Symbols]
    {n : ℕ} (p : T.CompleteType (Fin n)) (hp : ¬ CompleteTypeIsIsolated p) :
    ∃ N : T.ModelType.{0, 0, 0}, Countable N ∧ p ∉ T.realizedTypes N (Fin n) := by
  classical
  let Requirement := L.Formula (ℕ ⊕ Unit) ⊕ (Fin n → ℕ)
  let U : Requirement → Set (T.CompleteType ℕ) :=
    Sum.elim (withNamedWitness (T := T)) (omitNamedTuple p)
  have hU : ∀ r, IsOpen (U r) := fun r => Sum.casesOn r isOpen_withNamedWitness (isOpen_omitNamedTuple p)
  have hd : ∀ r, Dense (U r) := fun r => Sum.casesOn r dense_withNamedWitness (dense_omitNamedTuple p hp)
  have hsat : T.IsSatisfiable := Language.Theory.CompleteType.nonempty_iff.mp ⟨p⟩
  have : Nonempty (T.CompleteType ℕ) := Language.Theory.CompleteType.nonempty_iff.mpr hsat
  obtain ⟨q, hq⟩ := (dense_iInter_of_isOpen hU hd).nonempty
  obtain ⟨M, a, rfl⟩ := T.exists_modelType_is_realized_in q
  have hmeet : L.MeetsDefinable (Set.range a) :=
    range_meetsDefinable a fun ψ => Set.mem_iInter.mp hq (Sum.inl ψ)
  let S := hmeet.toElementarySubstructure
  let N := S.toModel T
  have hS : (S : Set M) = Set.range a := hmeet.closure_eq_self
  have hcount : Countable N := by
    change Countable S
    exact Set.countable_coe_iff.mpr (hS ▸ Set.countable_range a)
  refine ⟨N, hcount, ?_⟩
  rintro ⟨v, hv⟩
  have hname (i : Fin n) : (v i).val ∈ Set.range a := hS ▸ (v i).property
  choose s hs using hname
  have he : a ∘ s = S.subtype ∘ v := funext hs
  have ht : T.typeOf (a ∘ s) = p := by
    let v' : Fin n → S := v
    have he' : a ∘ s = S.subtype ∘ v' := he
    calc
      T.typeOf (a ∘ s) = T.typeOf (S.subtype ∘ v') := congrArg (fun u => T.typeOf u) he'
      _ = T.typeOf v' := typeOf_elementaryEmbedding S.subtype v'
      _ = p := hv
  have homit := Set.mem_iInter.mp hq (Sum.inr s)
  change T.typeOf a ∈ omitNamedTuple p s at homit
  obtain ⟨ψ, hψ⟩ := Set.mem_iUnion.mp homit
  obtain ⟨hψp, hbad⟩ := Set.mem_iUnion.mp hψ
  have hnot : ψ.not.Realize (a ∘ s) := by
    have h := Language.Theory.CompleteType.formula_mem_typeOf.mp hbad
    rwa [Language.Formula.realize_relabel] at h
  have hgood : ψ.Realize (a ∘ s) :=
    Language.Theory.CompleteType.formula_mem_typeOf.mp (by rwa [ht])
  exact Language.Formula.realize_not.mp hnot hgood

/-- Every complete finite type of a countably categorical theory with an
infinite model is isolated. -/
theorem completeTypeIsIsolated_of_countablyCategorical
    {M : Type} [L.Structure M] [Countable M] [Infinite M]
    [Countable L.Symbols] (hCat : (ℵ₀ : Cardinal.{0}).Categorical (L.completeTheory M))
    {n : ℕ} (p : (L.completeTheory M).CompleteType (Fin n)) :
    CompleteTypeIsIsolated p := by
  classical
  by_contra hp
  let T := L.completeTheory M
  have hL : L.card ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr inferInstance
  obtain ⟨N, hcount, hN⟩ := exists_countable_model_omits_completeType p hp
  have hMN : M ≅[L] N := Language.elementarilyEquivalent_iff.mpr fun φ =>
    (Language.realize_iff_of_model_completeTheory M N φ).symm
  have : Infinite N := hMN.infinite
  obtain ⟨e⟩ := hCat (Language.Theory.ModelType.of T M) N
    (by change #M = ℵ₀; exact Cardinal.mk_eq_aleph0 M)
    (Cardinal.mk_eq_aleph0 N)
  obtain ⟨a, ha⟩ := surjective_typeOf_of_countablyCategorical hL hCat n p
  exact hN ⟨e ∘ a, (typeOf_elementaryEmbedding e.toElementaryEmbedding a).trans ha⟩

/-- A countably categorical theory has finitely many complete types in
every finite arity. -/
theorem finite_completeType_of_countablyCategorical
    {M : Type} [L.Structure M] [Countable M] [Infinite M]
    [Countable L.Symbols] (hCat : (ℵ₀ : Cardinal.{0}).Categorical (L.completeTheory M)) (n : ℕ) :
    Finite ((L.completeTheory M).CompleteType (Fin n)) :=
  finite_completeType_of_isolated (completeTypeIsIsolated_of_countablyCategorical hCat)

/-- The complete theory of a countably infinite categorical structure has
finite covers by realised tuple types at each arity. -/
theorem finite_formula_type_covers_of_countablyCategorical
    {M : Type} [L.Structure M] [Countable M] [Infinite M] [Countable L.Symbols]
    (hCat : (ℵ₀ : Cardinal.{0}).Categorical (L.completeTheory M)) :
    ∀ n : ℕ, ∃ R : Finset (Fin n → M),
      ∀ b : Fin n → M, ∃ a : R, SameFormulaType (L := L) a.val b := by
  classical
  intro n
  let T := L.completeTheory M
  let P := T.CompleteType (Fin n)
  have : Finite P := finite_completeType_of_countablyCategorical hCat n
  let : Fintype P := Fintype.ofFinite _
  have hL : L.card ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.mpr inferInstance
  have htype := surjective_typeOf_of_countablyCategorical hL hCat n
  let rep (p : P) : Fin n → M := (htype p).choose
  refine ⟨Finset.univ.image rep, fun b => ?_⟩
  let p := T.typeOf b
  refine ⟨⟨rep p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩⟩, fun φ => ?_⟩
  have heq : T.typeOf (rep p) = T.typeOf b := (htype p).choose_spec
  refine (Language.Theory.CompleteType.formula_mem_typeOf (T := T) (v := rep p) (φ := φ)).symm.trans ?_
  rw [heq]
  exact Language.Theory.CompleteType.formula_mem_typeOf

/-- The converse of Ryll–Nardzewski for countable languages. The
automorphism group of a countably infinite categorical structure has
finitely many orbits of tuples of each finite arity. -/
theorem finite_tupleOrbitRepresentatives_of_categorical_completeTheory
    {M : Type} [L.Structure M] [Countable M] [Infinite M] [Countable L.Symbols]
    (hCat : (ℵ₀ : Cardinal.{0}).Categorical (L.completeTheory M)) (n : ℕ) :
    ∃ R : Finset (Fin n → M), ∀ x : Fin n → M,
      ∃ r ∈ R, ∃ g : FirstOrderAut L M, g • r = x := by
  have hc := finite_formula_type_covers_of_countablyCategorical hCat
  obtain ⟨R, hR⟩ := hc n
  refine ⟨R, fun b => ?_⟩
  obtain ⟨a, ha⟩ := hR b
  exact ⟨a.val, a.property, exists_aut_of_sameFormulaType_of_finite_formula_type_covers hc ha⟩

end SuccessorTree.NonPrecompact
