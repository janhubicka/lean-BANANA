import BANANA.NonPrecompact.FirstOrderDefinableTupleRamsey
import Mathlib.ModelTheory.Types

/-!
# Invariant types from definable tuple Ramsey

Type isolation lets matching parameter tuples extend to matching finite
contexts. Definable tuple Ramsey makes such contexts agree on any finite
set of invariance conditions. First-order compactness then gives an
invariant complete type.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

universe u v w a

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- A matching subtuple extends to a matching copy of its finite context
when the type of that context is isolated by one formula. -/
theorem SameFormulaType.exists_extend_of_isolates
    {r k : ℕ} (b : Fin r → M) (i : Fin k → Fin r) (d : Fin k → M)
    (h : SameFormulaType (L := L) (b ∘ i) d)
    (θ : L.Formula (Fin r)) (hθ : ∀ z : Fin r → M, θ.Realize z ↔ SameFormulaType (L := L) b z) :
    ∃ b' : Fin r → M, SameFormulaType (L := L) b b' ∧ b' ∘ i = d := by
  let ψ : L.Formula (Fin k ⊕ Fin r) := θ.relabel Sum.inr ⊓
    Language.Formula.iInf fun j : Fin k =>
      (Language.Term.var (Sum.inr (i j))).equal (Language.Term.var (Sum.inl j))
  have characterize (q : Fin k → M) (z : Fin r → M) :
      ψ.Realize (Sum.elim q z) ↔ SameFormulaType (L := L) b z ∧ z ∘ i = q := by
    simp only [ψ, Language.Formula.realize_inf, Language.Formula.realize_relabel, Sum.elim_comp_inr,
      Language.Formula.realize_iInf, Language.Formula.realize_equal, Language.Term.realize_var,
      Sum.elim_inl, Sum.elim_inr, funext_iff, Function.comp_apply, hθ]
  have hex : (ψ.iExs (Fin r)).Realize (b ∘ i) :=
    Language.Formula.realize_iExs.mpr ⟨b, (characterize _ _).2 ⟨SameFormulaType.refl _, rfl⟩⟩
  obtain ⟨z, hz⟩ := Language.Formula.realize_iExs.mp ((h _).mp hex)
  exact ⟨z, (characterize _ _).1 hz⟩

private abbrev FiniteTypeExtension (L : Language.{u, v}) (M : Type w) [L.Structure M] : Prop :=
  ∀ {r k : ℕ} (b : Fin r → M) (i : Fin k → Fin r) (d : Fin k → M),
    SameFormulaType (L := L) (b ∘ i) d →
    ∃ b' : Fin r → M, SameFormulaType (L := L) b b' ∧ b' ∘ i = d

private theorem finiteTypeExtension_of_isolated
    (h : ∀ r (b : Fin r → M), ∃ θ : L.Formula (Fin r),
      ∀ z : Fin r → M, θ.Realize z ↔ SameFormulaType (L := L) b z) :
    FiniteTypeExtension L M := by
  intro r k b i d hMatch
  obtain ⟨θ, hθ⟩ := h r b
  exact SameFormulaType.exists_extend_of_isolates b i d hMatch θ hθ

/-- The definable tuple Ramsey property makes finitely many parameter
type invariance requirements consistent with any formula in the type
of a fixed tuple. The parameter pairs may have different arities. -/
private theorem exists_realize_fin_invariance
    (hRamsey : HasDefinableTupleRamsey L M) (hExtend : FiniteTypeExtension L M)
    {k c : ℕ} (x : Fin k → M) (δ : L.Formula (Fin k)) (hδ : δ.Realize x)
    (l : Fin c → ℕ) (b d : ∀ j, Fin (l j) → M)
    (matchType : ∀ j, SameFormulaType (L := L) (b j) (d j))
    (φ : ∀ j, L.Formula (Fin (l j) ⊕ Fin k)) :
    ∃ x' : Fin k → M, δ.Realize x' ∧
      ∀ j, (φ j).Realize (Sum.elim (b j) x') ↔ (φ j).Realize (Sum.elim (d j) x') := by
  classical
  let I := Σ j : Fin c, Fin (l j)
  let ie : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let pick (j : Fin c) (i : Fin (l j)) : Fin (Fintype.card I) := ie ⟨j, i⟩
  let a : Fin (Fintype.card I) → M := fun i => b (ie.symm i).1 (ie.symm i).2
  have a_pick (j : Fin c) : a ∘ pick j = b j := by
    funext i
    change b (ie.symm (ie ⟨j, i⟩)).1 (ie.symm (ie ⟨j, i⟩)).2 = b j i
    rw [_root_.Equiv.symm_apply_apply]
  choose a' ha' da' using fun j =>
    hExtend a (pick j) (d j) (by rw [a_pick]; exact matchType j)
  let J := Option (Fin c) × Fin (Fintype.card I)
  let je : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let insert (j : Option (Fin c)) (i : Fin (Fintype.card I)) : Fin (Fintype.card J) := je (j, i)
  let B : Fin (Fintype.card J) → M := fun i =>
    (Option.elim (je.symm i).1 a a') (je.symm i).2
  have B_insert (j : Option (Fin c)) : B ∘ insert j = Option.elim j a a' := by
    funext i
    change Option.elim (je.symm (je (j, i))).1 a a' (je.symm (je (j, i))).2 = _
    rw [_root_.Equiv.symm_apply_apply]
  let colour (j : Fin c) : L.Formula (Fin (Fintype.card I) ⊕ Fin k) :=
    (φ j).relabel (Sum.map (pick j) id)
  obtain ⟨B', hB', hmono⟩ := hRamsey a B x colour
  have mono (j : Fin c) :
      (φ j).Realize (Sum.elim (B' ∘ insert none ∘ pick j) x) ↔
        (φ j).Realize (Sum.elim (B' ∘ insert (some j) ∘ pick j) x) := by
    have h₁ : SameFormulaType (L := L) a (B ∘ insert none) := by
      rw [B_insert]
      exact SameFormulaType.refl _
    have h₂ : SameFormulaType (L := L) a (B ∘ insert (some j)) := by
      rw [B_insert]
      exact ha' j
    have h := hmono (insert none) (insert (some j)) h₁ h₂ j
    have realization (s : Fin (Fintype.card I) → M) :
        (colour j).Realize (Sum.elim s x) ↔ (φ j).Realize (Sum.elim (s ∘ pick j) x) := by
      simp only [colour, Language.Formula.realize_relabel, Sum.elim_comp_map, Function.comp_id]
    exact (realization _).symm.trans (h.trans (realization _))
  let place (j : Fin c) (s : Option (Fin c)) : L.Formula (Fin (Fintype.card J) ⊕ Fin k) :=
    (φ j).relabel (Sum.map (insert s ∘ pick j) id)
  let ψ : L.Formula (Fin (Fintype.card J) ⊕ Fin k) := δ.relabel Sum.inr ⊓
    Language.Formula.iInf (fun j : Fin c => (place j none).iff (place j (some j)))
  have realize_ψ (z : Fin (Fintype.card J) → M) (y : Fin k → M) :
      ψ.Realize (Sum.elim z y) ↔ δ.Realize y ∧
        ∀ j, (φ j).Realize (Sum.elim (z ∘ insert none ∘ pick j) y) ↔
          (φ j).Realize (Sum.elim (z ∘ insert (some j) ∘ pick j) y) := by
    simp only [ψ, place, Language.Formula.realize_inf, Language.Formula.realize_iInf,
      Language.Formula.realize_iff, Language.Formula.realize_relabel,
      Sum.elim_comp_inr, Sum.elim_comp_map, Function.comp_id]
  have hψ : (ψ.iExs (Fin k)).Realize B' :=
    Language.Formula.realize_iExs.mpr ⟨x, (realize_ψ _ _).2 ⟨hδ, mono⟩⟩
  obtain ⟨x', hx'⟩ := Language.Formula.realize_iExs.mp ((hB' _).mpr hψ)
  obtain ⟨hδ', hmatch⟩ := (realize_ψ _ _).mp hx'
  refine ⟨x', hδ', fun j => ?_⟩
  simpa only [← Function.comp_assoc, B_insert, Option.elim_none, Option.elim_some, a_pick, da']
    using hmatch j

private theorem exists_realize_invariance
    (hRamsey : HasDefinableTupleRamsey L M) (hExtend : FiniteTypeExtension L M)
    {α : Type a} [Nonempty M] {c : ℕ} (x : α → M) (δ : L.Formula α) (hδ : δ.Realize x)
    (l : Fin c → ℕ) (b d : ∀ j, Fin (l j) → M)
    (matchType : ∀ j, SameFormulaType (L := L) (b j) (d j))
    (φ : ∀ j, L.Formula (Fin (l j) ⊕ α)) :
    ∃ x' : α → M, δ.Realize x' ∧
      ∀ j, (φ j).Realize (Sum.elim (b j) x') ↔ (φ j).Realize (Sum.elim (d j) x') := by
  classical
  let S := δ.freeVarFinset ∪ Finset.univ.biUnion fun j : Fin c =>
    (φ j).freeVarFinset.preimage Sum.inr Sum.inr_injective.injOn
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  have hδS : ↑δ.freeVarFinset ⊆ (S : Set α) := Finset.coe_subset.mpr Finset.subset_union_left
  let δf : L.Formula (Fin (Fintype.card S)) := δ.restrictFreeVar (e ∘ Set.inclusion hδS)
  have φS (j : Fin c) {z : α} (hz : Sum.inr z ∈ (φ j).freeVarFinset) : z ∈ S :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, Finset.mem_preimage.mpr hz⟩)
  let index (j : Fin c) (z : (φ j).freeVarFinset) : Fin (l j) ⊕ Fin (Fintype.card S) :=
    match z with
    | ⟨Sum.inl t, _⟩ => Sum.inl t
    | ⟨Sum.inr t, ht⟩ => Sum.inr (e ⟨t, φS j ht⟩)
  let φf (j : Fin c) : L.Formula (Fin (l j) ⊕ Fin (Fintype.card S)) :=
    (φ j).restrictFreeVar (index j)
  let padding : M := Classical.choice ‹Nonempty M›
  let lift (y : Fin (Fintype.card S) → M) (z : α) : M :=
    if hz : z ∈ S then y (e ⟨z, hz⟩) else padding
  have δ_realize (y : Fin (Fintype.card S) → M) (z : α → M)
      (hz : ∀ t : S, y (e t) = z t) : δf.Realize y ↔ δ.Realize z :=
    Language.BoundedFormula.realize_restrictFreeVar z fun t => hz (Set.inclusion hδS t)
  have φ_realize (j : Fin c) (p : Fin (l j) → M)
      (y : Fin (Fintype.card S) → M) (z : α → M)
      (hz : ∀ t : S, y (e t) = z t) :
      (φf j).Realize (Sum.elim p y) ↔ (φ j).Realize (Sum.elim p z) := by
    apply Language.BoundedFormula.realize_restrictFreeVar
    rintro ⟨t | t, ht⟩
    · rfl
    · exact hz ⟨t, φS j ht⟩
  let xf := x ∘ ((↑) : S → α) ∘ e.symm
  have hxf (t : S) : xf (e t) = x t := by simp [xf]
  obtain ⟨y, hy, hm⟩ := exists_realize_fin_invariance hRamsey hExtend xf δf
    ((δ_realize xf x hxf).mpr hδ) l b d matchType φf
  have hlift (t : S) : y (e t) = lift y t := by simp [lift, t.property]
  refine ⟨lift y, (δ_realize y _ hlift).mp hy, fun j => ?_⟩
  exact (φ_realize j (b j) y _ hlift).symm.trans
    ((hm j).trans (φ_realize j (d j) y _ hlift))

/-- Substitute named model parameters into a formula while keeping its other free variables. -/
def formulaWithParameters {α : Type a} {β : Type*} (φ : L.Formula (β ⊕ α))
    (b : β → M) : L[[M]].Formula α :=
  Language.BoundedFormula.constantsVarsEquiv.symm (φ.relabel (Sum.map b id))

@[simp]
theorem realize_formulaWithParameters {α : Type a} {β : Type*} (φ : L.Formula (β ⊕ α))
    (b : β → M) (x : α → M) :
    (formulaWithParameters φ b).Realize x ↔ φ.Realize (Sum.elim b x) := by
  have h : (φ.relabel (Sum.map b id)).Realize
      (Sum.elim (fun a : M => (L.con a : M)) x) ↔
      (formulaWithParameters φ b).Realize x := by
    simpa only [formulaWithParameters, _root_.Equiv.apply_symm_apply, Language.Formula.Realize] using
      (Language.BoundedFormula.realize_constantsVarsEquiv
        (φ := formulaWithParameters φ b) (v := x) (xs := default))
  have hAssignment :
      Sum.elim (fun a : M => (L.con a : M)) x ∘ Sum.map b id = Sum.elim b x := by
    funext t
    cases t <;> rfl
  rw [Language.Formula.realize_relabel, hAssignment] at h
  exact h.symm

/-- Invariance under matching finite parameter types in the model.
On a strongly finitely homogeneous model this is automorphism invariance. -/
def IsInvariantType {α : Type a} (p : (L.elementaryDiagram M).CompleteType α) : Prop :=
  ∀ {n : ℕ} (φ : L.Formula (Fin n ⊕ α)) (b d : Fin n → M),
    SameFormulaType (L := L) b d →
      (Language.Formula.equivSentence (formulaWithParameters φ b) ∈ p ↔
        Language.Formula.equivSentence (formulaWithParameters φ d) ∈ p)

/-- Invariant types agree on named formulas when an automorphism acts
on their parameter tuples. -/
theorem IsInvariantType.mem_formulaWithParameters_iff_aut {α : Type a}
    {p : (L.elementaryDiagram M).CompleteType α} (hp : IsInvariantType p)
    (g : M ≃[L] M) {n : ℕ} (φ : L.Formula (Fin n ⊕ α)) (b : Fin n → M) :
    Language.Formula.equivSentence (formulaWithParameters φ b) ∈ p ↔
      Language.Formula.equivSentence (formulaWithParameters φ (g ∘ b)) ∈ p :=
  hp φ b (g ∘ b) fun ψ => (Language.StrongHomClass.realize_formula g ψ).symm

private structure InvarianceCondition (L : Language.{u, v}) (M : Type w)
    [L.Structure M] (α : Type a) where
  arity : ℕ
  formula : L.Formula (Fin arity ⊕ α)
  left : Fin arity → M
  right : Fin arity → M
  matchType : SameFormulaType (L := L) left right

private def InvarianceCondition.sentence {α : Type a} (q : InvarianceCondition L M α) :
    L[[M]][[α]].Sentence :=
  (Language.Formula.equivSentence (formulaWithParameters q.formula q.left)).iff
    (Language.Formula.equivSentence (formulaWithParameters q.formula q.right))

private theorem exists_finite_preimages {A B : Type*} [DecidableEq B]
    {f : A → B} {t : Finset B} (h : (↑t : Set B) ⊆ Set.range f) :
    ∃ s : Finset A, s.image f = t := by
  rw [← Set.image_univ] at h
  obtain ⟨s, _, hs⟩ := Finset.subset_set_image_iff.mp h
  exact ⟨s, hs⟩

private theorem exists_invariantType_of_finitely_realized
    (hRamsey : HasDefinableTupleRamsey L M)
    (hIsolate : ∀ r (b : Fin r → M), ∃ θ : L.Formula (Fin r),
      ∀ z : Fin r → M, θ.Realize z ↔ SameFormulaType (L := L) b z)
    {α : Type a} [Nonempty M] (S : Set (L.Formula α))
    (hBase : ∀ Δ : Finset S, ∃ x : α → M,
      (Language.Formula.iInf fun d : Δ => d.val.val).Realize x) :
    ∃ p : (L.elementaryDiagram M).CompleteType α, IsInvariantType p ∧
      ∀ (φ : L.Formula α), φ ∈ S →
        Language.Formula.equivSentence ((L.lhomWithConstants M).onFormula φ) ∈ p := by
  classical
  let T := L.elementaryDiagram M
  let base (δ : S) : L[[M]][[α]].Sentence :=
    Language.Formula.equivSentence ((L.lhomWithConstants M).onFormula δ.val)
  let req := Set.range base ∪ Set.range (InvarianceCondition.sentence (L := L) (M := M) (α := α))
  have hs : ((L[[M]].lhomWithConstants α).onTheory T ∪ req).IsSatisfiable := by
    apply Language.Theory.isSatisfiable_iff_isFinitelySatisfiable.mpr
    intro t ht
    let tBase := t.filter (· ∈ Set.range base)
    let tCond := t.filter
      (· ∈ Set.range (InvarianceCondition.sentence (L := L) (M := M) (α := α)))
    obtain ⟨D, hD⟩ := exists_finite_preimages (f := base) (t := tBase)
      (fun _ hx => (Finset.mem_filter.mp hx).2)
    obtain ⟨Q, hQ⟩ := exists_finite_preimages
      (f := InvarianceCondition.sentence (L := L) (M := M) (α := α)) (t := tCond)
      (fun _ hx => (Finset.mem_filter.mp hx).2)
    let δ : L.Formula α := Language.Formula.iInf fun s : D => s.val.val
    obtain ⟨x, hδ⟩ := hBase D
    let e : Fin (Fintype.card Q) ≃ Q := (Fintype.equivFin Q).symm
    let q (j : Fin (Fintype.card Q)) := (e j).val
    obtain ⟨y, hy, hm⟩ := exists_realize_invariance hRamsey
      (finiteTypeExtension_of_isolated hIsolate) x δ hδ
      (fun j => (q j).arity) (fun j => (q j).left) (fun j => (q j).right)
      (fun j => (q j).matchType) (fun j => (q j).formula)
    let : (Language.constantsOn α).Structure M := Language.constantsOn.structure y
    let : M ⊨ (t : L[[M]][[α]].Theory) := ⟨fun ψ hψt => by
      rcases ht hψt with hψ | hψ | hψ
      · exact (Language.LHom.onTheory_model _ _).2 (inferInstance : M ⊨ T) |>.realize_of_mem _ hψ
      · have hp : ψ ∈ tBase := Finset.mem_filter.mpr ⟨hψt, hψ⟩
        rw [← hD] at hp
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hp
        exact (Language.Formula.realize_equivSentence _ _).mpr
          ((Language.LHom.realize_onFormula _ _).mpr
            (Language.Formula.realize_iInf.mp hy ⟨d, hd⟩))
      · have hp : ψ ∈ tCond := Finset.mem_filter.mpr ⟨hψt, hψ⟩
        rw [← hQ] at hp
        obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨j, hj⟩ := e.surjective ⟨q₀, hq₀⟩
        have hjq : q j = q₀ := congrArg Subtype.val hj
        have h : (q j).formula.Realize (Sum.elim (q j).left y) ↔
            (q j).formula.Realize (Sum.elim (q j).right y) := hm j
        rw [hjq] at h
        have hyName (a : α) : (L[[M]].con a : M) = y a := rfl
        simpa only [InvarianceCondition.sentence, Language.Sentence.realize_iff,
          Language.Formula.realize_equivSentence, realize_formulaWithParameters, hyName] using h⟩
    exact Language.Theory.Model.isSatisfiable M
  have hnonempty : ({p : T.CompleteType α | req ⊆ ↑p} : Set _).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro h
    exact (Language.Theory.CompleteType.setOfPred_subset_eq_empty_iff (T := T) req).mp h hs
  obtain ⟨p, hp⟩ := hnonempty
  refine ⟨p, ?_, fun φ hφ => hp (Or.inl ⟨⟨φ, hφ⟩, rfl⟩)⟩
  intro n φ b d hbd
  let q : InvarianceCondition L M α := ⟨n, φ, b, d, hbd⟩
  have hq : q.sentence ∈ p := hp (Or.inr ⟨q, rfl⟩)
  let N := p.isMaximal.1.some
  have mem_iff (ψ : L[[M]][[α]].Sentence) : ψ ∈ p ↔ N ⊨ ψ :=
    (p.isMaximal.mem_iff_models ψ).trans (p.isMaximal.isComplete.realize_sentence_iff ψ N).symm
  have hreal := (mem_iff _).mp hq
  simp only [InvarianceCondition.sentence, Language.Sentence.realize_iff] at hreal
  exact (mem_iff _).trans (hreal.trans (mem_iff _).symm)

/-- In a model with isolated finite tuple types, definable tuple Ramsey yields
a complete type over the model that extends the parameter-free type of any
tuple and is invariant under matching finite parameter types. The tuple may
enumerate the entire model. -/
theorem HasDefinableTupleRamsey.exists_invariantType
    (hRamsey : HasDefinableTupleRamsey L M)
    (hIsolate : ∀ r (b : Fin r → M), ∃ θ : L.Formula (Fin r),
      ∀ z : Fin r → M, θ.Realize z ↔ SameFormulaType (L := L) b z)
    {α : Type a} [Nonempty M] (x : α → M) :
    ∃ p : (L.elementaryDiagram M).CompleteType α, IsInvariantType p ∧
      ∀ (φ : L.Formula α), φ.Realize x →
        Language.Formula.equivSentence ((L.lhomWithConstants M).onFormula φ) ∈ p :=
  exists_invariantType_of_finitely_realized hRamsey hIsolate {φ | φ.Realize x}
    fun _ => ⟨x, Language.Formula.realize_iInf.mpr fun s => s.val.property⟩

private theorem exists_realize_iff_realize_exClosure {α : Type a} [DecidableEq α] [Nonempty M]
    (φ : L.Formula α) : (∃ x : α → M, φ.Realize x) ↔ φ.exClosure.Realize M := by
  classical
  rw [← Language.Formula.exists_realize_equivSentence_iff_realize_exClosure (φ := φ)]
  refine exists_congr fun x => ?_
  simpa only [_root_.Equiv.symm_apply_apply] using
    (Language.Formula.realize_equivSentence_symm M (Language.Formula.equivSentence φ) x)

/-- Every complete type over the empty set extends to a complete type over
a model with definable tuple Ramsey and isolated finite tuple types.
The extension is invariant under matching finite parameter types. -/
theorem HasDefinableTupleRamsey.exists_invariantExtension
    (hRamsey : HasDefinableTupleRamsey L M)
    (hIsolate : ∀ r (b : Fin r → M), ∃ θ : L.Formula (Fin r),
      ∀ z : Fin r → M, θ.Realize z ↔ SameFormulaType (L := L) b z)
    {α : Type a} [Nonempty M] (p₀ : (L.completeTheory M).CompleteType α) :
    ∃ p : (L.elementaryDiagram M).CompleteType α, IsInvariantType p ∧
      ∀ (φ : L.Formula α), Language.Formula.equivSentence φ ∈ p₀ →
        Language.Formula.equivSentence ((L.lhomWithConstants M).onFormula φ) ∈ p := by
  classical
  apply exists_invariantType_of_finitely_realized (α := α) hRamsey hIsolate
    {φ | Language.Formula.equivSentence φ ∈ p₀}
  intro Δ
  let δ : L.Formula α := Language.Formula.iInf fun d : Δ => d.val.val
  obtain ⟨N, x, hx⟩ := Language.Theory.exists_modelType_is_realized_in (L.completeTheory M) p₀
  have hmem (φ : L.Formula α) : Language.Formula.equivSentence φ ∈ p₀ ↔ φ.Realize x := by
    rw [← hx]
    exact Language.Theory.CompleteType.formula_mem_typeOf
  have hδ : δ.Realize x :=
    Language.Formula.realize_iInf.mpr fun d => (hmem d.val.val).mp d.val.property
  exact (exists_realize_iff_realize_exClosure (M := M) δ).mpr <|
    (Language.realize_iff_of_model_completeTheory M N _).mp <|
      (exists_realize_iff_realize_exClosure (M := (N : Type _)) δ).mp ⟨x, hδ⟩

end SuccessorTree.NonPrecompact
