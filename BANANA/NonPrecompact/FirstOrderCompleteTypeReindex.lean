import Mathlib.ModelTheory.Topology.Types
import BANANA.NonPrecompact.FirstOrderInvariantEnumerationRamseySaturated

/-!
# Reindexing variables in complete types

Pullback along a language map preserves complete types when it sends the
base theory into the target theory. Reindexing the named variables is one
instance, and is continuous for the topology of formula membership.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder Set
open scoped FirstOrder

universe u v u' v' a b w w'

variable {L : Language.{u, v}} {K : Language.{u', v'}}
  {T : L.Theory} {R : K.Theory} {α : Type a} {β : Type b}

/-- Pull back a complete type along a language map which preserves the base theory. -/
def completeTypePullback (f : L[[β]] →ᴸ K[[α]])
    (hf : f.onTheory ((L.lhomWithConstants β).onTheory T) ⊆
      (K.lhomWithConstants α).onTheory R) (p : R.CompleteType α) : T.CompleteType β where
  toTheory := f.onSentence ⁻¹' (p : K[[α]].Theory)
  subset' := fun φ hφ => p.subset (hf ⟨φ, hφ, rfl⟩)
  isMaximal' := by
    refine ⟨?_, fun φ => p.mem_or_not_mem (f.onSentence φ)⟩
    apply Language.Theory.isSatisfiable_of_isSatisfiable_onTheory f
    exact p.isMaximal.1.mono (image_preimage_subset _ _)

@[simp]
theorem mem_completeTypePullback (f : L[[β]] →ᴸ K[[α]])
    (hf : f.onTheory ((L.lhomWithConstants β).onTheory T) ⊆
      (K.lhomWithConstants α).onTheory R)
    (p : R.CompleteType α) (φ : L[[β]].Sentence) :
    φ ∈ completeTypePullback f hf p ↔ f.onSentence φ ∈ p := Iff.rfl

/-- Pullback of complete types is continuous in the formula-membership topology. -/
theorem continuous_completeTypePullback (f : L[[β]] →ᴸ K[[α]])
    (hf : f.onTheory ((L.lhomWithConstants β).onTheory T) ⊆
      (K.lhomWithConstants α).onTheory R) :
    Continuous (completeTypePullback f hf) := by
  apply CompleteType.isTopologicalBasis_range_typesWith.continuous_iff.mpr
  rintro _ ⟨φ, rfl⟩
  exact CompleteType.isOpen_typesWith (f.onSentence φ)

private theorem typeReindex_base (f : β → α) :
    (L.lhomWithConstantsMap f).onTheory ((L.lhomWithConstants β).onTheory T) ⊆
      (L.lhomWithConstants α).onTheory T := by
  rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
  refine ⟨φ, hφ, ?_⟩
  change (L.lhomWithConstants α).onBoundedFormula φ =
    (L.lhomWithConstantsMap f).onBoundedFormula ((L.lhomWithConstants β).onBoundedFormula φ)
  rw [← Function.comp_apply (f := (L.lhomWithConstantsMap f).onBoundedFormula),
    ← Language.LHom.comp_onBoundedFormula]
  change (L.lhomWithConstants α).onBoundedFormula φ =
    ((L.lhomWithConstantsMap f).comp Language.LHom.sumInl).onBoundedFormula φ
  rw [Language.LHom.map_constants_comp_sumInl]

/-- Reindex a complete type by taking the listed coordinates, with repetitions allowed. -/
def completeTypeReindex (f : β → α) (p : T.CompleteType α) : T.CompleteType β :=
  completeTypePullback (L.lhomWithConstantsMap f) (typeReindex_base f) p

/-- Variable reindexing of complete types is continuous. -/
theorem continuous_completeTypeReindex (T : L.Theory) (f : β → α) :
    Continuous (completeTypeReindex (T := T) f) :=
  continuous_completeTypePullback _ (typeReindex_base f)

/-- Reindexing a realised type is the type of the reindexed assignment. -/
theorem completeTypeReindex_typeOf {M : Type w} [L.Structure M] [Nonempty M] [M ⊨ T]
    (f : β → α) (v : α → M) :
    completeTypeReindex f (T.typeOf v) = T.typeOf (v ∘ f) := by
  let _ : (Language.constantsOn α).Structure M := Language.constantsOn.structure v
  let _ : (Language.constantsOn β).Structure M := Language.constantsOn.structure (v ∘ f)
  let _ : (Language.LHom.constantsOnMap f).IsExpansionOn M :=
    Language.constantsOnMap_isExpansionOn (f := f) rfl
  let _ : (L.lhomWithConstantsMap f).IsExpansionOn M :=
    Language.LHom.sumMap_isExpansionOn _ _ M
  apply SetLike.ext
  intro φ
  change (L.lhomWithConstantsMap f).onSentence φ ∈ T.typeOf v ↔ φ ∈ T.typeOf (v ∘ f)
  exact Language.LHom.realize_onSentence M (L.lhomWithConstantsMap f) φ

@[simp]
theorem formula_mem_completeTypeReindex (f : β → α) (p : T.CompleteType α) (φ : L.Formula β) :
    Language.Formula.equivSentence φ ∈ completeTypeReindex f p ↔
      Language.Formula.equivSentence (φ.relabel f) ∈ p := by
  obtain ⟨M, v, rfl⟩ := T.exists_modelType_is_realized_in p
  rw [completeTypeReindex_typeOf, Language.Theory.CompleteType.formula_mem_typeOf,
    Language.Theory.CompleteType.formula_mem_typeOf, Language.Formula.realize_relabel]

/-- Reindexing the variables of a type leaves its named parameters alone. -/
theorem mem_completeTypeReindex_formulaWithParameters {M : Type w} [L.Structure M]
    (f : β → α) (p : (L.elementaryDiagram M).CompleteType α)
    {ι : Type*} (φ : L.Formula (ι ⊕ β)) (d : ι → M) :
    Language.Formula.equivSentence (formulaWithParameters φ d) ∈ completeTypeReindex f p ↔
      Language.Formula.equivSentence (formulaWithParameters (φ.relabel (Sum.map id f)) d) ∈ p := by
  obtain ⟨N, v, rfl⟩ := (L.elementaryDiagram M).exists_modelType_is_realized_in p
  let _ : L.Structure N := (L.lhomWithConstants M).reduct N
  rw [completeTypeReindex_typeOf, Language.Theory.CompleteType.formula_mem_typeOf,
    Language.Theory.CompleteType.formula_mem_typeOf, realize_formulaWithParameters_of_expansion,
    realize_formulaWithParameters_of_expansion, Language.Formula.realize_relabel]
  have hcoords :
      Sum.elim (fun i => (L.con (d i) : N)) v ∘ Sum.map id f =
        Sum.elim (fun i => (L.con (d i) : N)) (v ∘ f) := by
    funext i
    cases i <;> rfl
  rw [hcoords]

/-- Reindexing variables preserves invariance under all model automorphisms. -/
theorem IsAutomorphismInvariantType.reindex {M : Type w} [L.Structure M]
    {p : (L.elementaryDiagram M).CompleteType α} (hp : IsAutomorphismInvariantType p)
    (f : β → α) : IsAutomorphismInvariantType (completeTypeReindex f p) := by
  intro g n φ d
  rw [mem_completeTypeReindex_formulaWithParameters, mem_completeTypeReindex_formulaWithParameters]
  exact hp g _ d

/-- A formula with an arbitrary stock of parameters depends on a finite
tuple of them. The same presentation works for every interpretation of
the parameters and free variables. -/
theorem exists_finite_parameter_formula {ι : Type w} (φ : L.Formula (ι ⊕ α)) :
    ∃ (n : ℕ) (ψ : L.Formula (Fin n ⊕ α)) (d : Fin n → ι),
      ∀ {N : Type w'} [L.Structure N] (k : ι → N) (x : α → N),
        φ.Realize (Sum.elim k x) ↔ ψ.Realize (Sum.elim (k ∘ d) x) := by
  classical
  let s := φ.freeVarFinset.preimage Sum.inl Sum.inl_injective.injOn
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let index (z : φ.freeVarFinset) : Fin (Fintype.card s) ⊕ α :=
    match z with
    | ⟨Sum.inl a, ha⟩ => Sum.inl (e ⟨a, Finset.mem_preimage.mpr ha⟩)
    | ⟨Sum.inr a, _⟩ => Sum.inr a
  refine ⟨_, φ.restrictFreeVar index, fun i => (e.symm i).val, fun {N} _ k x => ?_⟩
  symm
  apply Language.BoundedFormula.realize_restrictFreeVar
  rintro ⟨a | a, ha⟩
  · change k (e.symm (e ⟨a, Finset.mem_preimage.mpr ha⟩)).val = k a
    rw [_root_.Equiv.symm_apply_apply]
  · rfl

end SuccessorTree.NonPrecompact
