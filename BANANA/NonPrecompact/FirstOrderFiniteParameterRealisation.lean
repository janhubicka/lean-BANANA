import BANANA.NonPrecompact.FirstOrderInvariantEnumerationRamseySaturated

/-!
# Realising types over finite parameter tuples

A complete type over a finite parameter tuple can be realised in a model
whose complete theory has finite covers by realised types. The joint type
of the parameters and a witness is isolated in a model of the expanded
theory, so its existential closure transfers to the original model with
the same named parameters.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder Function
open scoped FirstOrder
open Language Theory

universe u v w

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] [Nonempty M]

/-- Finite covers of the realised tuple types give realisation of all
complete types of finite tuples over finite sets of parameters. -/
theorem realizesFiniteParameterTypes_of_finite_type_covers
    (cover : ∀ n : ℕ, ∃ R : Finset (Fin n → M),
      ∀ b : Fin n → M, ∃ a : R, SameFormulaType (L := L) a.val b) :
    RealizesFiniteParameterTypes L M := by
  intro k r d
  dsimp only
  let _ : (constantsOn (Fin k)).Structure M := constantsOn.structure d
  let K := L[[Fin k]]
  let T := K.completeTheory M
  intro p
  obtain ⟨N, b, htype⟩ := T.exists_modelType_is_realized_in p
  let inc := L.lhomWithConstants (Fin k)
  let _ : L.Structure N := inc.reduct N
  have hEq : M ≅[L] N := by
    apply Language.elementarilyEquivalent_iff.mpr
    intro φ
    exact (LHom.realize_onSentence M inc φ).symm.trans <|
      (Language.realize_iff_of_model_completeTheory M N (inc.onSentence φ)).symm.trans
        (LHom.realize_onSentence N inc φ)
  let dN : Fin k → N := fun i => (L.con i : N)
  let e : Fin k ⊕ Fin r ≃ Fin (k + r) := finSumFinEquiv
  let bN := Sum.elim dN b ∘ e.symm
  obtain ⟨R, hR⟩ := cover (k + r)
  obtain ⟨a₀, ha₀⟩ :=
    finite_formula_type_cover_of_elementarilyEquivalent hEq (fun x : R => x.val) hR bN
  obtain ⟨θ, hθ⟩ :=
    exists_formula_isolates_in_finite_type_cover (fun x : R => x.val) hR a₀.val
  let χ := θ.relabel e.symm
  have hvN : χ.Realize (Sum.elim dN b) := by
    rw [Formula.realize_relabel]
    exact (isolates_formula_type_of_elementarilyEquivalent hEq hθ bN).2 ha₀
  let sentence := Formula.equivSentence (χ.iExs (Fin r))
  have hN : sentence.Realize N :=
    (Formula.realize_equivSentence N (χ.iExs (Fin r))).2
    (Formula.realize_iExs.2 ⟨b, hvN⟩)
  have hM : sentence.Realize M :=
    (Language.realize_iff_of_model_completeTheory M N sentence).1 hN
  have hMv : (χ.iExs (Fin r)).Realize d :=
    (Formula.realize_equivSentence M (χ.iExs (Fin r))).1 hM
  obtain ⟨a, ha⟩ := Formula.realize_iExs.1 hMv
  have ha' : θ.Realize (Sum.elim d a ∘ e.symm) := by
    simpa only [χ, Formula.realize_relabel] using ha
  have hjoint : SameFormulaType (L := L) (Sum.elim d a ∘ e.symm) bN :=
    ((hθ _).1 ha').symm.trans ha₀
  refine ⟨a, ?_⟩
  rw [← htype]
  apply SetLike.ext
  intro σ
  obtain ⟨ψ, rfl⟩ := Formula.equivSentence.surjective σ
  rw [CompleteType.formula_mem_typeOf, CompleteType.formula_mem_typeOf]
  let ξ : L.Formula (Fin k ⊕ Fin r) := BoundedFormula.constantsVarsEquiv ψ
  have hmatch := hjoint (ξ.relabel e)
  simp only [Formula.realize_relabel] at hmatch
  have hMcomp : (Sum.elim d a ∘ e.symm) ∘ e = Sum.elim d a := by
    funext x
    exact congrArg (Sum.elim d a) (e.symm_apply_apply x)
  have hNcomp : bN ∘ e = Sum.elim dN b := by
    funext x
    exact congrArg (Sum.elim dN b) (e.symm_apply_apply x)
  rw [hMcomp, hNcomp] at hmatch
  exact (BoundedFormula.realize_constantsVarsEquiv (φ := ψ) (v := a) (xs := default)).symm.trans <|
    hmatch.trans (BoundedFormula.realize_constantsVarsEquiv (φ := ψ) (v := b) (xs := default))

end SuccessorTree.NonPrecompact
