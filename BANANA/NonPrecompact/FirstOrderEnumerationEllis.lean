import BANANA.NonPrecompact.FirstOrderCompleteTypeReindex

/-!
# The Ellis-map condition on first-order enumeration types

With finite-parameter saturation and strong finite homogeneity, the types of
automorphic enumerations are dense among the extensions of the enumeration
type. Evaluation on the compact pointwise closure lifts every invariant
enumeration type to an Ellis map. On realised enumeration types its value is
the corresponding reindexing of the invariant type.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder
open Language Theory
open Set Function

universe u v w a

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- The complete types over a model in variables indexed by its elements. -/
abbrev EnumerationTypes (L : Language.{u,v}) (M : Type w) [L.Structure M] :=
  (L.elementaryDiagram M).CompleteType M

/-- A type of an enumeration extends the parameter-free type of the model itself. -/
def ExtendsEnumerationType (p : EnumerationTypes L M) : Prop :=
  ∀ (φ : L.Formula M), φ.Realize (id : M → M) →
    Formula.equivSentence ((L.lhomWithConstants M).onFormula φ) ∈ p

private abbrev parameterMap (g : M ≃[L] M) :=
  L.lhomWithConstantsMap (g : M → M)

private theorem realize_parameterMap_formula {N : Type*} [L.Structure N] [old : L[[M]].Structure N]
    [hbase : (L.lhomWithConstants M).IsExpansionOn N] {α : Type a} (g : M ≃[L] M)
    (φ : L[[M]].Formula α) (x : α → N) :
    ((parameterMap g).onFormula φ).Realize x ↔
      (Language.BoundedFormula.constantsVarsEquiv φ).Realize
        (Sum.elim (fun m => (L.con (g m) : N)) x) default := by
  let N' := (parameterMap g).reduct N
  have hExpansion : @LHom.IsExpansionOn L L[[M]] (L.lhomWithConstants M) N _ N' := by
    constructor
    · intro n f xs
      exact hbase.map_onFunction f xs
    · intro n r xs
      exact hbase.map_onRelation r xs
  have ho := @LHom.realize_onFormula _ _ N N' α old (parameterMap g)
    (@LHom.isExpansionOn_reduct _ _ (parameterMap g) N old) φ x
  let _ : L[[M]].Structure N := N'
  let _ : (L.lhomWithConstants M).IsExpansionOn N := hExpansion
  exact ho.trans (Language.BoundedFormula.realize_constantsVarsEquiv (φ := φ)
    (v := x) (xs := default)).symm

private theorem parameterMap_preserves_diagram (g : M ≃[L] M) :
    (parameterMap g).onTheory (L.elementaryDiagram M) ⊆ L.elementaryDiagram M := by
  rintro _ ⟨φ, hφ, rfl⟩
  have hφM : φ.Realize M := hφ
  change ((parameterMap g).onSentence φ).Realize M
  rw [Language.LHom.onSentence, Sentence.Realize, realize_parameterMap_formula]
  have hc := (Language.StrongHomClass.realize_formula g
    (show L.Formula (M ⊕ Empty) from Language.BoundedFormula.constantsVarsEquiv φ)
    (v := Sum.elim id (default : Empty → M)))
  have hs : (g : M → M) ∘ Sum.elim id (default : Empty → M) =
      Sum.elim (fun m => (L.con (g m) : M)) (default : Empty → M) := by
    funext x
    cases x with
    | inl x => rfl
    | inr x => exact x.elim
  rw [← hs]
  exact hc.mpr ((Language.BoundedFormula.realize_constantsVarsEquiv (φ := φ)
    (v := (default : Empty → M)) (xs := default)).mpr hφM)

private theorem parameterMap_preserves_typeBase (g : M ≃[L] M) :
    ((parameterMap g).addConstants M).onTheory
        ((L[[M]].lhomWithConstants M).onTheory (L.elementaryDiagram M)) ⊆
      (L[[M]].lhomWithConstants M).onTheory (L.elementaryDiagram M) := by
  rintro _ ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
  refine ⟨_, parameterMap_preserves_diagram (L := L) g ⟨φ, hφ, rfl⟩, ?_⟩
  simp only [LHom.onSentence, LHom.onFormula]
  change ((L[[M]].lhomWithConstants M).onBoundedFormula ∘
    (parameterMap g).onBoundedFormula) φ =
      (((parameterMap g).addConstants M).onBoundedFormula ∘
        (L[[M]].lhomWithConstants M).onBoundedFormula) φ
  simp only [← LHom.comp_onBoundedFormula]
  have hmap : ((parameterMap g).addConstants M).comp (L[[M]].lhomWithConstants M) =
      (L[[M]].lhomWithConstants M).comp (parameterMap g) :=
    LHom.sumMap_comp_inl (parameterMap g) (LHom.id (constantsOn M))
  exact congrArg (fun f : L[[M]] →ᴸ L[[M]][[M]] => f.onBoundedFormula φ) hmap.symm

/-- An automorphism acts on types by pulling their parameters back by its inverse. -/
def enumerationTypeAction (g : M ≃[L] M) (p : EnumerationTypes L M) :
    EnumerationTypes L M :=
  completeTypePullback ((parameterMap g.symm).addConstants M)
    (parameterMap_preserves_typeBase g.symm) p

private theorem mem_typeOf_addConstants {K K' : Language} {T : K'.Theory}
    {N : Type*} [K'.Structure N] [Nonempty N] [N ⊨ T] {α : Type a}
    (ρ : K →ᴸ K') (φ : K.Formula α) (x : α → N) :
    ((ρ.addConstants α).onSentence (Formula.equivSentence φ)) ∈ T.typeOf x ↔
      (ρ.onFormula φ).Realize x := by
  let _ : (constantsOn α).Structure N := constantsOn.structure x
  let _ : K.Structure N := ρ.reduct N
  exact (LHom.realize_onSentence N (ρ.addConstants α) _).trans
    ((Formula.realize_equivSentence N φ).trans (ρ.realize_onFormula φ).symm)

/-- Rename a formula's parameters by the inverse automorphism when testing the action image. -/
theorem mem_enumerationTypeAction_formula (g : M ≃[L] M) (p : EnumerationTypes L M)
    (φ : L[[M]].Formula M) :
    Formula.equivSentence φ ∈ enumerationTypeAction g p ↔
      Formula.equivSentence ((parameterMap g.symm).onFormula φ) ∈ p := by
  obtain ⟨N, v, rfl⟩ := (L.elementaryDiagram M).exists_modelType_is_realized_in p
  exact (mem_typeOf_addConstants (T := L.elementaryDiagram M) (parameterMap g.symm) φ v).trans
    (CompleteType.formula_mem_typeOf (T := L.elementaryDiagram M)).symm

/-- Each named formula tests a finite parameter tuple, including after an automorphism acts. -/
theorem mem_enumerationTypeAction_formulaWithParameters (g : M ≃[L] M)
    (p : EnumerationTypes L M) {n : ℕ} (φ : L.Formula (Fin n ⊕ M)) (d : Fin n → M) :
    Formula.equivSentence (formulaWithParameters φ d) ∈ enumerationTypeAction g p ↔
      Formula.equivSentence (formulaWithParameters φ (g.symm ∘ d)) ∈ p := by
  rw [mem_enumerationTypeAction_formula]
  obtain ⟨N, v, rfl⟩ := (L.elementaryDiagram M).exists_modelType_is_realized_in p
  let _ : L.Structure N := (L.lhomWithConstants M).reduct N
  rw [CompleteType.formula_mem_typeOf, CompleteType.formula_mem_typeOf,
    realize_parameterMap_formula, realize_formulaWithParameters_of_expansion]
  simp only [formulaWithParameters, _root_.Equiv.apply_symm_apply]
  change (φ.relabel (Sum.map d id)).Realize
      (Sum.elim (fun m => (L.con (g.symm m) : N)) v) ↔ _
  rw [Formula.realize_relabel, Sum.elim_comp_map, Function.comp_id]
  rfl

private theorem exists_parameterTuple_for_enumerationSentence (ψ : L[[M]][[M]].Sentence) :
    ∃ (n : ℕ) (φ : L.Formula (Fin n ⊕ M)) (d : Fin n → M),
      ∀ q : EnumerationTypes L M,
        ψ ∈ q ↔ Formula.equivSentence (formulaWithParameters φ d) ∈ q := by
  let θ : L[[M]].Formula M := Formula.equivSentence.symm ψ
  let ξ : L.Formula (M ⊕ M) := Language.BoundedFormula.constantsVarsEquiv θ
  obtain ⟨n, φ, d, h⟩ := exists_finite_parameter_formula ξ
  refine ⟨n, φ, d, fun q => ?_⟩
  obtain ⟨N, v, rfl⟩ := (L.elementaryDiagram M).exists_modelType_is_realized_in q
  let _ : L.Structure N := (L.lhomWithConstants M).reduct N
  rw [CompleteType.mem_typeOf, CompleteType.formula_mem_typeOf,
    realize_formulaWithParameters_of_expansion]
  exact Language.BoundedFormula.realize_constantsVarsEquiv.symm.trans
    (h (fun m => (L.con m : N)) v)

/-- Automorphism-invariant enumeration types are exactly the points fixed by the action. -/
theorem isAutomorphismInvariantType_iff_fixedEnumerationType (p : EnumerationTypes L M) :
    IsAutomorphismInvariantType p ↔ ∀ g : M ≃[L] M, enumerationTypeAction g p = p := by
  constructor
  · intro hp g
    apply SetLike.ext
    intro ψ
    obtain ⟨n, φ, d, h⟩ := exists_parameterTuple_for_enumerationSentence ψ
    rw [h, h, mem_enumerationTypeAction_formulaWithParameters]
    exact (hp g.symm φ d).symm
  · intro hp g n φ d
    have h := mem_enumerationTypeAction_formulaWithParameters g.symm p φ d
    rw [hp, Language.Equiv.symm_symm] at h
    exact h

/-- The identity automorphism fixes every enumeration type. -/
theorem enumerationTypeAction_refl (p : EnumerationTypes L M) :
    enumerationTypeAction (.refl L M) p = p := by
  apply SetLike.ext
  intro ψ
  obtain ⟨n, φ, d, h⟩ := exists_parameterTuple_for_enumerationSentence ψ
  rw [h, h, mem_enumerationTypeAction_formulaWithParameters]
  rfl

/-- The parameter action respects composition of automorphisms. -/
theorem enumerationTypeAction_comp (g k : M ≃[L] M) (p : EnumerationTypes L M) :
    enumerationTypeAction (g.comp k) p =
      enumerationTypeAction g (enumerationTypeAction k p) := by
  apply SetLike.ext
  intro ψ
  obtain ⟨n, φ, d, h⟩ := exists_parameterTuple_for_enumerationSentence ψ
  rw [h, h, mem_enumerationTypeAction_formulaWithParameters,
    mem_enumerationTypeAction_formulaWithParameters,
    mem_enumerationTypeAction_formulaWithParameters]
  rfl

/-- On realised types the action is composition of the tuple with the automorphism. -/
theorem enumerationTypeAction_typeOf [Nonempty M] (g : M ≃[L] M) (x : M → M) :
    enumerationTypeAction g ((L.elementaryDiagram M).typeOf x) =
      (L.elementaryDiagram M).typeOf (g ∘ x) := by
  apply SetLike.ext
  intro ψ
  obtain ⟨φ, rfl⟩ := Formula.equivSentence.surjective ψ
  rw [mem_enumerationTypeAction_formula, CompleteType.formula_mem_typeOf,
    CompleteType.formula_mem_typeOf, realize_parameterMap_formula]
  let ξ : L.Formula (M ⊕ M) := Language.BoundedFormula.constantsVarsEquiv φ
  have hcomp : g ∘ Sum.elim (fun m => (L.con (g.symm m) : M)) x =
      Sum.elim (fun m => (L.con m : M)) (g ∘ x) := by
    funext i
    cases i with
    | inl m => exact g.apply_symm_apply m
    | inr m => rfl
  exact (Language.StrongHomClass.realize_formula g ξ).symm.trans
    ((Iff.of_eq (congrArg (Formula.Realize ξ) hcomp)).trans
      Language.BoundedFormula.realize_constantsVarsEquiv)

/-- Finite parameter type-realisation and finite homogeneity make the orbit of
the realised enumeration dense in its space of type extensions. -/
theorem enumerationExtension_mem_closure_automorphismTypes [Nonempty M]
    (hSat : RealizesFiniteParameterTypes L M)
    (hHom : ∀ n (x y : Fin n → M), SameFormulaType (L := L) x y →
      ∃ g : M ≃[L] M, g ∘ x = y)
    {p : EnumerationTypes L M} (hp : ExtendsEnumerationType p) :
    p ∈ closure (range (fun g : M ≃[L] M =>
      (L.elementaryDiagram M).typeOf (g : M → M))) := by
  classical
  apply CompleteType.isTopologicalBasis_range_typesWith.mem_closure_iff.mpr
  rintro _ ⟨ψ, rfl⟩ hψ
  change ψ ∈ p at hψ
  let θ : L[[M]].Formula M := Formula.equivSentence.symm ψ
  let ξ : L.Formula (M ⊕ M) := Language.BoundedFormula.constantsVarsEquiv θ
  obtain ⟨N, v, hv⟩ := (L.elementaryDiagram M).exists_modelType_is_realized_in p
  let _ : L.Structure N := (L.lhomWithConstants M).reduct N
  let e := Language.ElementaryEmbedding.ofModelsElementaryDiagram L M N
  have hθ : θ.Realize v := by
    apply (CompleteType.formula_mem_typeOf (T := L.elementaryDiagram M)).mp
    rw [hv]
    simpa only [θ, _root_.Equiv.apply_symm_apply] using hψ
  have hξ : ξ.Realize (Sum.elim (e : M → N) v) :=
    Language.BoundedFormula.realize_constantsVarsEquiv.mpr hθ
  let S := ξ.freeVarFinset.image (Sum.elim id id)
  let equivFin : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  let labels : Fin (Fintype.card S) → M := Subtype.val ∘ equivFin.symm
  let index (x : ξ.freeVarFinset) : Fin (Fintype.card S) ⊕ Fin (Fintype.card S) :=
    match x with
    | ⟨Sum.inl i, hi⟩ => Sum.inl (equivFin ⟨i, Finset.mem_image_of_mem _ hi⟩)
    | ⟨Sum.inr i, hi⟩ => Sum.inr (equivFin ⟨i, Finset.mem_image_of_mem _ hi⟩)
  let η : L.Formula (Fin (Fintype.card S) ⊕ Fin (Fintype.card S)) := ξ.restrictFreeVar index
  have hIndex (t : ξ.freeVarFinset) : Sum.map labels labels (index t) = t.val := by
    rcases t with ⟨i | i, hi⟩ <;> simp [index, labels]
  have realizationN : η.Realize (Sum.elim (e ∘ labels) (v ∘ labels)) ↔
      ξ.Realize (Sum.elim e v) := by
    apply Language.BoundedFormula.realize_restrictFreeVar
    intro t
    rw [← Sum.elim_comp_map, Function.comp_apply, hIndex]
  obtain ⟨τ, hτ⟩ := hSat.exists_matching_tuple e labels (v ∘ labels)
  have hSame : SameFormulaType (L := L) labels τ := by
    intro φ
    have base (φ : L.Formula (Fin (Fintype.card S))) :
        φ.Realize labels → φ.Realize (v ∘ labels) := by
      intro hφ
      have hφ' : (φ.relabel labels).Realize (id : M → M) := by
        simpa only [Formula.realize_relabel, id_comp] using hφ
      have hm := hp _ hφ'
      rw [← hv] at hm
      exact Formula.realize_relabel.mp ((L.lhomWithConstants M).realize_onFormula _
        |>.mp (CompleteType.formula_mem_typeOf.mp hm))
    have hvτ : φ.Realize τ ↔ φ.Realize (v ∘ labels) := by
      simpa only [Formula.realize_relabel, Sum.elim_comp_inr] using hτ (φ.relabel Sum.inr)
    refine ⟨fun h => hvτ.mpr (base φ h), fun h => ?_⟩
    by_contra hn
    exact (base φ.not hn) (hvτ.mp h)
  obtain ⟨g, hg⟩ := hHom _ labels τ hSame
  have hξg : ξ.Realize (Sum.elim id (g : M → M)) := by
    have realizationM : η.Realize (Sum.elim labels (g ∘ labels)) ↔
        ξ.Realize (Sum.elim id (g : M → M)) := by
      apply Language.BoundedFormula.realize_restrictFreeVar
      intro t
      change (Sum.elim (id ∘ labels) (g ∘ labels)) (index t) = _
      rw [← Sum.elim_comp_map, Function.comp_apply, hIndex]
    exact realizationM.mp (hg ▸ (hτ η).mpr (realizationN.mpr hξ))
  have hθg : θ.Realize (g : M → M) :=
    Language.BoundedFormula.realize_constantsVarsEquiv.mp hξg
  refine ⟨(L.elementaryDiagram M).typeOf (g : M → M), ?_, ⟨g, rfl⟩⟩
  exact CompleteType.mem_typeOf.mpr hθg


/-- Extending the parameter-free enumeration type is a closed condition. -/
theorem isClosed_extendsEnumerationType :
    IsClosed {p : EnumerationTypes L M | ExtendsEnumerationType p} := by
  have hSet : {p : EnumerationTypes L M | ExtendsEnumerationType p} =
      ⋂ (φ : L.Formula M) (_ : φ.Realize (id : M → M)),
        (L.elementaryDiagram M).typesWith
          (Formula.equivSentence ((L.lhomWithConstants M).onFormula φ)) := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, CompleteType.mem_typesWith_iff,
      ExtendsEnumerationType]
  rw [hSet]
  exact isClosed_iInter fun φ => isClosed_iInter fun _ => CompleteType.isClosed_typesWith _

/-- The type of an automorphic enumeration extends the original enumeration type. -/
theorem automorphismType_extendsEnumerationType [Nonempty M] (g : M ≃[L] M) :
    ExtendsEnumerationType ((L.elementaryDiagram M).typeOf (g : M → M)) := by
  intro φ hφ
  rw [CompleteType.formula_mem_typeOf, LHom.realize_onFormula]
  exact (Language.StrongHomClass.realize_formula g φ (v := id)).mpr hφ

/-- The usual action on enumeration types is continuous in each group element. -/
theorem continuous_enumerationTypeAction (g : M ≃[L] M) :
    Continuous (enumerationTypeAction g) :=
  continuous_completeTypePullback _ (parameterMap_preserves_typeBase g.symm)

/-- The closed space of extensions of the parameter-free enumeration type. -/
abbrev EnumerationTypeSpace (L : Language.{u,v}) (M : Type w) [L.Structure M] :=
  {p : EnumerationTypes L M // ExtendsEnumerationType p}

/-- The pointwise action maps on the closed enumeration type space. -/
def enumerationTypeSpaceAction [Nonempty M] (hSat : RealizesFiniteParameterTypes L M)
    (hHom : ∀ n (x y : Fin n → M), SameFormulaType (L := L) x y →
      ∃ g : M ≃[L] M, g ∘ x = y)
    (g : M ≃[L] M) (p : EnumerationTypeSpace L M) :
    EnumerationTypeSpace L M := by
  refine ⟨enumerationTypeAction g p.val, ?_⟩
  have h : IsClosed ((enumerationTypeAction g) ⁻¹'
      {q : EnumerationTypes L M | ExtendsEnumerationType q}) :=
    isClosed_extendsEnumerationType.preimage (continuous_enumerationTypeAction g)
  apply closure_minimal _ h (enumerationExtension_mem_closure_automorphismTypes hSat hHom p.property)
  rintro _ ⟨k, rfl⟩
  change ExtendsEnumerationType (enumerationTypeAction g ((L.elementaryDiagram M).typeOf k))
  rw [enumerationTypeAction_typeOf]
  exact automorphismType_extendsEnumerationType (g.comp k)

@[simp]
theorem enumerationTypeSpaceAction_refl [Nonempty M]
    (hSat : RealizesFiniteParameterTypes L M)
    (hHom : ∀ n (x y : Fin n → M), SameFormulaType (L := L) x y →
      ∃ g : M ≃[L] M, g ∘ x = y)
    (p : EnumerationTypeSpace L M) :
    enumerationTypeSpaceAction hSat hHom (.refl L M) p = p :=
  Subtype.ext (enumerationTypeAction_refl p.val)

theorem enumerationTypeSpaceAction_comp [Nonempty M]
    (hSat : RealizesFiniteParameterTypes L M)
    (hHom : ∀ n (x y : Fin n → M), SameFormulaType (L := L) x y →
      ∃ g : M ≃[L] M, g ∘ x = y)
    (g k : M ≃[L] M) (p : EnumerationTypeSpace L M) :
    enumerationTypeSpaceAction hSat hHom (g.comp k) p =
      enumerationTypeSpaceAction hSat hHom g (enumerationTypeSpaceAction hSat hHom k p) :=
  Subtype.ext (enumerationTypeAction_comp g k p.val)

/-- The pointwise closure of the action maps is closed under composition. -/
theorem comp_mem_enumerationEllisSemigroup [Nonempty M]
    (hSat : RealizesFiniteParameterTypes L M)
    (hHom : ∀ n (x y : Fin n → M), SameFormulaType (L := L) x y →
      ∃ g : M ≃[L] M, g ∘ x = y)
    {f g : EnumerationTypeSpace L M → EnumerationTypeSpace L M}
    (hf : f ∈ closure (range (enumerationTypeSpaceAction hSat hHom)))
    (hg : g ∈ closure (range (enumerationTypeSpaceAction hSat hHom))) :
    f ∘ g ∈ closure (range (enumerationTypeSpaceAction hSat hHom)) := by
  let X := EnumerationTypeSpace L M
  let a := enumerationTypeSpaceAction hSat hHom
  let E : Set (X → X) := closure (range a)
  show f ∈ (fun k : X → X => k ∘ g) ⁻¹' E
  apply closure_minimal _ (isClosed_closure.preimage (Pi.continuous_precomp g)) hf
  rintro _ ⟨k, rfl⟩
  show g ∈ (fun h : X → X => a k ∘ h) ⁻¹' E
  have hc : Continuous (a k) :=
    ((continuous_enumerationTypeAction k).comp continuous_subtype_val).subtype_mk _
  apply closure_minimal _
    (isClosed_closure.preimage (continuous_pi fun x => hc.comp (continuous_apply x))) hg
  rintro _ ⟨l, rfl⟩
  apply subset_closure
  refine ⟨k.comp l, ?_⟩
  funext p
  exact enumerationTypeSpaceAction_comp hSat hHom k l p

/-- An invariant enumeration type gives an element of the pointwise closure
of the action maps taking every realised enumeration extension to an invariant
type. The converse is evaluation at the type of the original enumeration. -/
theorem exists_invariantEnumerationType_iff_exists_ellisMap [Nonempty M]
    (hSat : RealizesFiniteParameterTypes L M)
    (hHom : ∀ n (x y : Fin n → M), SameFormulaType (L := L) x y →
      ∃ g : M ≃[L] M, g ∘ x = y) :
    (∃ p : EnumerationTypeSpace L M, IsAutomorphismInvariantType p.val) ↔
      ∃ η : EnumerationTypeSpace L M → EnumerationTypeSpace L M,
        η ∈ closure (range (enumerationTypeSpaceAction hSat hHom)) ∧
        ∀ (x : M → M) (hx : ExtendsEnumerationType ((L.elementaryDiagram M).typeOf x)),
          IsAutomorphismInvariantType (η ⟨(L.elementaryDiagram M).typeOf x, hx⟩).val := by
  let X := EnumerationTypeSpace L M
  let _ : CompactSpace X :=
    isCompact_iff_compactSpace.mp isClosed_extendsEnumerationType.isCompact
  let idType : X :=
    ⟨(L.elementaryDiagram M).typeOf id, automorphismType_extendsEnumerationType (.refl L M)⟩
  let a := enumerationTypeSpaceAction hSat hHom
  constructor
  · rintro ⟨p, hp⟩
    let eval (f : X → X) : EnumerationTypes L M := (f idType).val
    have hEval : Continuous eval := continuous_subtype_val.comp (continuous_apply idType)
    have hOrbit : eval '' range a = range (fun g : M ≃[L] M =>
        (L.elementaryDiagram M).typeOf (g : M → M)) := by
      rw [← Set.range_comp]
      congr 1
      funext g
      change enumerationTypeAction g ((L.elementaryDiagram M).typeOf id) = _
      rw [enumerationTypeAction_typeOf, Function.comp_id]
    have hpEval : p.val ∈ eval '' closure (range a) := by
      rw [← hEval.isClosedMap.closure_image_eq_of_continuous hEval, hOrbit]
      exact enumerationExtension_mem_closure_automorphismTypes hSat hHom p.property
    obtain ⟨η, hη, hpη⟩ := hpEval
    refine ⟨η, hη, fun x hx => ?_⟩
    let xType : X := ⟨(L.elementaryDiagram M).typeOf x, hx⟩
    have hAgreement : Set.EqOn (fun f : X → X => (f xType).val)
        (fun f : X → X => completeTypeReindex x (eval f)) (range a) := by
      rintro _ ⟨g, rfl⟩
      change enumerationTypeAction g ((L.elementaryDiagram M).typeOf x) =
        completeTypeReindex x (enumerationTypeAction g ((L.elementaryDiagram M).typeOf id))
      rw [enumerationTypeAction_typeOf, enumerationTypeAction_typeOf, completeTypeReindex_typeOf,
        Function.comp_id]
    have hh := (hAgreement.closure (continuous_subtype_val.comp (continuous_apply xType))
      ((continuous_completeTypeReindex (L.elementaryDiagram M) x).comp hEval)) hη
    change (η xType).val = completeTypeReindex x (eval η) at hh
    rw [hh, hpη]
    exact hp.reindex x
  · rintro ⟨η, _, hη⟩
    exact ⟨η idType, hη id idType.property⟩

/-- In a saturated, strongly finitely homogeneous model, the definable tuple
Ramsey property is equivalent to the Ellis-map condition on enumeration types. -/
theorem hasDefinableTupleRamsey_iff_exists_ellisMap [Nonempty M]
    (hSat : RealizesFiniteParameterTypes L M)
    (hHom : ∀ n (x y : Fin n → M), SameFormulaType (L := L) x y →
      ∃ g : M ≃[L] M, g ∘ x = y) :
    HasDefinableTupleRamsey L M ↔
      ∃ η : EnumerationTypeSpace L M → EnumerationTypeSpace L M,
        η ∈ closure (range (enumerationTypeSpaceAction hSat hHom)) ∧
        ∀ (x : M → M) (hx : ExtendsEnumerationType ((L.elementaryDiagram M).typeOf x)),
          IsAutomorphismInvariantType (η ⟨(L.elementaryDiagram M).typeOf x, hx⟩).val := by
  rw [← exists_invariantEnumerationType_iff_exists_ellisMap]
  apply (hasDefinableTupleRamsey_iff_exists_automorphismInvariantEnumerationType hSat hHom).trans
  constructor
  · rintro ⟨p, hp, hExt⟩
    exact ⟨⟨p, hExt⟩, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p.val, hp, p.property⟩

end SuccessorTree.NonPrecompact
