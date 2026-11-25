import BANANA.NonPrecompact.FirstOrderInvariantEnumerationRamsey

/-!
# The DEERP and invariant-type equivalence in saturated models

Finite-parameter type realisation and strong finite homogeneity give the
equivalence between definable tuple Ramsey and an automorphism-invariant
extension of the model's enumeration type.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

universe u v w w'

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- Every complete finite-tuple type over finitely many model parameters is realised. -/
def RealizesFiniteParameterTypes (L : Language.{u, v}) (M : Type w)
    [L.Structure M] [Nonempty M] : Prop :=
  ∀ {k r : ℕ} (d : Fin k → M),
    let _ : (Language.constantsOn (Fin k)).Structure M := Language.constantsOn.structure d
    ∀ q : ((L[[Fin k]]).completeTheory M).CompleteType (Fin r),
      q ∈ ((L[[Fin k]]).completeTheory M).realizedTypes M (Fin r)

/-- A finite tuple in an elementary extension can be matched over any finite parameter tuple
in a model that realises complete finite-parameter types. -/
theorem RealizesFiniteParameterTypes.exists_matching_tuple [Nonempty M]
    (hSat : RealizesFiniteParameterTypes L M)
    {N : Type w'} [L.Structure N] [Nonempty N] (e : M ↪ₑ[L] N)
    {k r : ℕ} (d : Fin k → M) (b : Fin r → N) :
    ∃ b' : Fin r → M, ∀ ψ : L.Formula (Fin k ⊕ Fin r),
      ψ.Realize (Sum.elim d b') ↔ ψ.Realize (Sum.elim (e ∘ d) b) := by
  let _ : (Language.constantsOn (Fin k)).Structure M := Language.constantsOn.structure d
  let _ : (Language.constantsOn (Fin k)).Structure N := Language.constantsOn.structure (e ∘ d)
  let T := (L[[Fin k]]).completeTheory M
  have hconM (i : Fin k) : (L.con i : M) = d i := rfl
  have hconN (i : Fin k) : (L.con i : N) = e (d i) := rfl
  let _ : N ⊨ T := ⟨fun σ hσ => by
    have hM : σ.Realize M := hσ
    have hf := (Language.BoundedFormula.realize_constantsVarsEquiv (φ := σ)
      (v := (default : Empty → M)) (xs := default)).mpr hM
    have hN := (e.map_formula (Language.BoundedFormula.constantsVarsEquiv σ)
      (Sum.elim d (default : Empty → M))).mpr (by
        simpa only [hconM, Language.Formula.Realize] using hf)
    apply (Language.BoundedFormula.realize_constantsVarsEquiv (φ := σ)
        (v := (default : Empty → N)) (xs := default)).mp
    have happ :
        e ∘ Sum.elim d (default : Empty → M) =
          Sum.elim (fun i => e (d i)) (default : Empty → N) := by
      funext x
      cases x with
      | inl i => rfl
      | inr y => exact y.elim
    simpa only [hconN, Language.Formula.Realize, happ] using hN⟩
  obtain ⟨b', hb'⟩ := hSat d (T.typeOf b)
  refine ⟨b', fun ψ => ?_⟩
  let ρ : L[[Fin k]].Formula (Fin r) := Language.BoundedFormula.constantsVarsEquiv.symm ψ
  have hr : ρ.Realize b' ↔ ρ.Realize b := by
    rw [← Language.Theory.CompleteType.formula_mem_typeOf (T := T) (v := b'),
      ← Language.Theory.CompleteType.formula_mem_typeOf (T := T) (v := b), hb']
  have hm : ψ.Realize (Sum.elim d b') ↔ ρ.Realize b' := by
    simpa only [ρ, _root_.Equiv.apply_symm_apply, hconM, Language.Formula.Realize] using
      (Language.BoundedFormula.realize_constantsVarsEquiv (φ := ρ) (v := b') (xs := default))
  have hn : ψ.Realize (Sum.elim (e ∘ d) b) ↔ ρ.Realize b := by
    simpa only [ρ, _root_.Equiv.apply_symm_apply, hconN, Function.comp_def, Language.Formula.Realize] using
      (Language.BoundedFormula.realize_constantsVarsEquiv (φ := ρ) (v := b) (xs := default))
  exact hm.trans (hr.trans hn.symm)


/-- The KLM reverse implication under finite-parameter type realisation and
strong finite homogeneity. -/
theorem HasDefinableTupleRamsey.of_invariantEnumerationType_of_finiteParameterTypes [Nonempty M]
    (hSat : RealizesFiniteParameterTypes L M)
    (hHom : ∀ n (x y : Fin n → M), SameFormulaType (L := L) x y →
      ∃ g : M ≃[L] M, g ∘ x = y)
    (q : (L.elementaryDiagram M).CompleteType M) (hq : IsInvariantType q)
    (hExt : ∀ (φ : L.Formula M), φ.Realize (id : M → M) →
      Language.Formula.equivSentence ((L.lhomWithConstants M).onFormula φ) ∈ q) :
    HasDefinableTupleRamsey L M := by
  intro l r k c a b d colour
  obtain ⟨_, _, _, e, dN, htype, hmonoN⟩ :=
    exists_colour_agreement_in_elementary_extension q hq hExt a b d colour
  obtain ⟨d', hmatch⟩ := hSat.exists_matching_tuple e b dN
  have hd : SameFormulaType (L := L) d' d := by
    intro ψ
    have h := hmatch (ψ.relabel Sum.inr)
    simp only [Language.Formula.realize_relabel, Sum.elim_comp_inr] at h
    exact h.trans (htype ψ).symm
  obtain ⟨g, hg⟩ := hHom k d' d hd
  refine ⟨g ∘ b, fun ψ => (Language.StrongHomClass.realize_formula g ψ).symm,
    fun i j hi hj t => ?_⟩
  have matchColour (x : Fin l → Fin r) :
      (colour t).Realize (Sum.elim (b ∘ x) d') ↔
        (colour t).Realize (Sum.elim ((e ∘ b) ∘ x) dN) := by
    simpa only [Language.Formula.realize_relabel, Sum.elim_comp_map, Function.comp_id]
      using hmatch ((colour t).relabel (Sum.map x id))
  have gColour (x : Fin l → Fin r) :
      (colour t).Realize (Sum.elim ((g ∘ b) ∘ x) d) ↔
        (colour t).Realize (Sum.elim (b ∘ x) d') := by
    have h : (g : M → M) ∘ Sum.elim (b ∘ x) d' =
        Sum.elim ((g ∘ b) ∘ x) d := by
      rw [← hg]
      exact funext fun s => by cases s <;> rfl
    simpa only [h] using
      (Language.StrongHomClass.realize_formula g (colour t) (v := Sum.elim (b ∘ x) d'))
  exact (gColour i).trans ((matchColour i).trans
    ((hmonoN ⟨i, hi⟩ ⟨j, hj⟩ t).trans ((matchColour j).symm.trans (gColour j).symm)))

/-- Automorphism invariance for a complete type over the model.
The parameters of any formula can be listed as a finite tuple. -/
def IsAutomorphismInvariantType {α : Type*} (p : (L.elementaryDiagram M).CompleteType α) : Prop :=
  ∀ (g : M ≃[L] M) {n : ℕ} (φ : L.Formula (Fin n ⊕ α)) (b : Fin n → M),
    Language.Formula.equivSentence (formulaWithParameters φ b) ∈ p ↔
      Language.Formula.equivSentence (formulaWithParameters φ (g ∘ b)) ∈ p

/-- In a strongly finitely homogeneous model, automorphism invariance is
the same as invariance under matching finite parameter types. -/
theorem isInvariantType_iff_isAutomorphismInvariantType
    (hHom : ∀ n (x y : Fin n → M), SameFormulaType (L := L) x y →
      ∃ g : M ≃[L] M, g ∘ x = y)
    {α : Type*} (p : (L.elementaryDiagram M).CompleteType α) :
    IsInvariantType p ↔ IsAutomorphismInvariantType p := by
  constructor
  · intro h g n φ b
    exact h.mem_formulaWithParameters_iff_aut g φ b
  · intro h n φ b d hbd
    obtain ⟨g, rfl⟩ := hHom n b d hbd
    exact h g φ b

/-- In a model with finite-parameter type realisation and strong finite
homogeneity, definable tuple Ramsey is equivalent to the existence of
an automorphism-invariant extension of the type of its enumeration. -/
theorem hasDefinableTupleRamsey_iff_exists_automorphismInvariantEnumerationType [Nonempty M]
    (hSat : RealizesFiniteParameterTypes L M)
    (hHom : ∀ n (x y : Fin n → M), SameFormulaType (L := L) x y →
      ∃ g : M ≃[L] M, g ∘ x = y) :
    HasDefinableTupleRamsey L M ↔
      ∃ q : (L.elementaryDiagram M).CompleteType M, IsAutomorphismInvariantType q ∧
        ∀ (φ : L.Formula M), φ.Realize (id : M → M) →
          Language.Formula.equivSentence ((L.lhomWithConstants M).onFormula φ) ∈ q := by
  constructor
  · intro h
    obtain ⟨q, hq, hExt⟩ := h.exists_invariantType_of_finiteHomogeneity hHom id
    exact ⟨q, (isInvariantType_iff_isAutomorphismInvariantType hHom q).mp hq, hExt⟩
  · rintro ⟨q, hq, hExt⟩
    exact HasDefinableTupleRamsey.of_invariantEnumerationType_of_finiteParameterTypes hSat hHom q
      ((isInvariantType_iff_isAutomorphismInvariantType hHom q).mpr hq) hExt

end SuccessorTree.NonPrecompact
