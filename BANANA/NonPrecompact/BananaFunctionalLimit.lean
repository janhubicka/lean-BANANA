import BANANA.NonPrecompact.BananaFirstOrderFunctional
import BANANA.NonPrecompact.BananaLimitFirstOrder
import BANANA.NonPrecompact.BananaLimitFiniteAge
import BANANA.NonPrecompact.BananaLimitGlobalHomogeneity
import BANANA.NonPrecompact.BananaLimitBilinearity
import BANANA.NonPrecompact.FirstOrderGradedAgeRepresentatives

/-!
# The explicit limit in the functional BANANA language

The closed substructures of the functional presentation are genuine pairs
of subspaces, including both zeroes. The native finite-age and homogeneity
proofs apply to this presentation.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder CategoryTheory
open scoped FirstOrder

namespace BananaFunctional

noncomputable instance limitStructure : bananaFunctionalLanguage.Structure BananaTaggedCarrier :=
  structureOn bananaLimitPairing

/-- A finite support block, on both sorts, is a functional substructure. -/
noncomputable def blockEmbedding (S : Finset ℚ) :
    @Language.Embedding bananaFunctionalLanguage
      ((bananaLimitBlock S) ⊕ (bananaLimitBlock S)) BananaTaggedCarrier
      (structureOn fun x y => bananaLimitPairing x y) limitStructure :=
  embedding _ _ _ _ (bananaLimitBlock S).injective_subtype (bananaLimitBlock S).injective_subtype
    (fun _ _ => rfl)

/-- The closure of every finite tagged set is supported on a single finite block. -/
theorem finite_of_fg (S : bananaFunctionalLanguage.Substructure BananaTaggedCarrier) (hS : S.FG) :
    Finite S := by
  classical
  obtain ⟨t, ht⟩ := hS
  let supports (x : BananaTaggedCarrier) : Finset ℚ := x.elim Finsupp.support Finsupp.support
  let U := t.biUnion supports
  let : bananaFunctionalLanguage.Structure
      ((bananaLimitBlock U) ⊕ (bananaLimitBlock U)) :=
    structureOn fun x y => bananaLimitPairing x y
  let b := blockEmbedding U
  have h₁ : (t : Set BananaTaggedCarrier) ⊆ b.toHom.range := by
    intro x hx
    cases x with
    | inl x =>
      refine ⟨Sum.inl ⟨x, ?_⟩, rfl⟩
      exact (bananaLimitBlock_mem_iff _ _).2 fun i hi =>
        Finset.mem_biUnion.mpr ⟨.inl x, hx, hi⟩
    | inr y =>
      refine ⟨Sum.inr ⟨y, ?_⟩, rfl⟩
      exact (bananaLimitBlock_mem_iff _ _).2 fun i hi =>
        Finset.mem_biUnion.mpr ⟨.inr y, hx, hi⟩
  have h₂ : S ≤ b.toHom.range := by
    rw [← ht]
    exact Language.Substructure.closure_le.mpr h₁
  let : Finite (bananaLimitBlock U) := by
    exact Finite.of_injective (bananaLimitBlockEquiv U) (bananaLimitBlockEquiv U).injective
  let : Finite b.toHom.range := Finite.of_surjective b.equivRange b.equivRange.surjective
  exact Finite.of_injective (S.inclusion h₂) (S.inclusion h₂).injective

/-- Native pairing automorphisms act on the functional tagged carrier. -/
noncomputable def aut (EL ER : BananaLimitVector ≃ₗ[F2] BananaLimitVector)
    (h : ∀ x y, bananaLimitPairing (EL x) (ER y) = bananaLimitPairing x y) :
    BananaTaggedCarrier ≃[bananaFunctionalLanguage] BananaTaggedCarrier :=
  let e := embedding bananaLimitPairing bananaLimitPairing EL.toLinearMap ER.toLinearMap
    EL.injective ER.injective h
  { toEquiv := EL.toEquiv.sumCongr ER.toEquiv
    map_fun' := e.map_fun
    map_rel' := e.map_rel }

/-- Linearising the explicit pairing in both arguments. -/
noncomputable def limitBilinear : BananaLimitVector →ₗ[F2] BananaLimitVector →ₗ[F2] F2 where
  toFun := bananaLimitPairingRightLinear
  map_add' x y := by
    apply LinearMap.ext
    intro z
    exact bananaLimitPairing_add_left x y z
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    exact bananaLimitPairing_smul_left c x z

/-- The inherited bilinear pairing on the native subspaces of a closed
substructure of the explicit limit. -/
noncomputable def restrictBilinear
    (S : bananaFunctionalLanguage.Substructure BananaTaggedCarrier) :
    leftSubspace bananaLimitPairing S →ₗ[F2] rightSubspace bananaLimitPairing S →ₗ[F2] F2 :=
  (limitBilinear.comp (leftSubspace bananaLimitPairing S).subtype).compl₂
    (rightSubspace bananaLimitPairing S).subtype

@[simp] theorem restrictBilinear_apply
    (S : bananaFunctionalLanguage.Substructure BananaTaggedCarrier)
    (x : leftSubspace bananaLimitPairing S) (y : rightSubspace bananaLimitPairing S) :
    restrictBilinear S x y = restrictedPairing bananaLimitPairing S x y := rfl

/-- The first-order isomorphism identifying an age member with its two
native subspaces of the concrete limit. -/
noncomputable def ageMemberEquiv (B : Bundled bananaFunctionalLanguage.Structure)
    (e : B ↪[bananaFunctionalLanguage] BananaTaggedCarrier) :
    let S := e.toHom.range
    letI := structureOn (restrictedPairing bananaLimitPairing S)
    B ≃[bananaFunctionalLanguage] ((leftSubspace bananaLimitPairing S) ⊕
      (rightSubspace bananaLimitPairing S)) := by
  letI := structureOn (restrictedPairing bananaLimitPairing e.toHom.range)
  exact (substructureEquiv bananaLimitPairing e.toHom.range).symm.comp e.equivRange

/-- The input isomorphism class of any element of the functional age is
determined by its finite native subspaces and their bilinear pairing. -/
theorem age_member_native (B : Bundled bananaFunctionalLanguage.Structure)
    (hB : B ∈ bananaFunctionalLanguage.age BananaTaggedCarrier) :
    ∃ S : bananaFunctionalLanguage.Substructure BananaTaggedCarrier, Finite S ∧
      letI := structureOn (restrictedPairing bananaLimitPairing S)
      Nonempty (B ≃[bananaFunctionalLanguage] ((leftSubspace bananaLimitPairing S) ⊕
        (rightSubspace bananaLimitPairing S))) := by
  let e := hB.2.some
  exact ⟨e.toHom.range, finite_of_fg _ (hB.1.range e.toHom), ⟨ageMemberEquiv B e⟩⟩

/-- The countable functional BANANA model is ultrahomogeneous. -/
theorem limit_ultrahomogeneous :
    bananaFunctionalLanguage.IsUltrahomogeneous BananaTaggedCarrier := by
  intro S hS f
  let U := leftSubspace bananaLimitPairing S
  let V := rightSubspace bananaLimitPairing S
  let : Finite S := finite_of_fg S hS
  let : Finite U := finite_leftSubspace bananaLimitPairing S
  let : Finite V := finite_rightSubspace bananaLimitPairing S
  obtain ⟨l, r, A, e, hL, hR⟩ := exists_finite_banana_substructure_of_limit U V
  let EL : (Fin l → F2) ≃ₗ[F2] U :=
    (LinearEquiv.ofInjective e.left e.left_injective).trans
      (LinearEquiv.ofEq _ _ hL)
  let ER : (Fin r → F2) ≃ₗ[F2] V :=
    (LinearEquiv.ofInjective e.right e.right_injective).trans
      (LinearEquiv.ofEq _ _ hR)
  let β := restrictedPairing bananaLimitPairing S
  let := structureOn A.eval
  let := structureOn β
  let p : (Fin l → F2) ⊕ (Fin r → F2) ≃[bananaFunctionalLanguage] U ⊕ V :=
    let ψ := embedding A.eval β EL.toLinearMap ER.toLinearMap
      EL.injective ER.injective e.pairing_apply
    { toEquiv := EL.toEquiv.sumCongr ER.toEquiv
      map_fun' := ψ.map_fun
      map_rel' := ψ.map_rel }
  let q := substructureEquiv bananaLimitPairing S
  let d := q.comp p
  let e' := f.comp d.toEmbedding
  have hleft : ∀ x, S.subtype (d (.inl x)) = Sum.inl (e.left x) := fun _ => rfl
  have hright : ∀ y, S.subtype (d (.inr y)) = Sum.inr (e.right y) := fun _ => rfl
  let e₂ : BananaMatrixEmbeddingToLimit A :=
    { left := leftLinear A.eval bananaLimitPairing e'
      right := rightLinear A.eval bananaLimitPairing e'
      left_injective := leftLinear_injective A.eval bananaLimitPairing e'
      right_injective := rightLinear_injective A.eval bananaLimitPairing e'
      pairing_apply := map_pairing A.eval bananaLimitPairing e' }
  obtain ⟨gL, gR, hp, hL', hR'⟩ := e.exists_global_pair_automorphism_extends e₂
  refine ⟨aut gL gR hp, ?_⟩
  apply Language.Embedding.ext
  intro x
  obtain ⟨x, rfl⟩ := d.surjective x
  cases x with
  | inl x =>
    change e' (.inl x) = (aut gL gR hp) (S.subtype (d (.inl x)))
    rw [map_inl_linear A.eval bananaLimitPairing e', hleft]
    exact congrArg Sum.inl (hL' x).symm
  | inr y =>
    change e' (.inr y) = (aut gL gR hp) (S.subtype (d (.inr y)))
    rw [map_inr_linear A.eval bananaLimitPairing e', hright]
    exact congrArg Sum.inr (hR' y).symm

/-- Native finite tuple orbits give a finite orbit cover in the functional language. -/
theorem finite_tuple_orbit_representatives (n : ℕ) :
    ∃ T : Finset (Fin n → BananaTaggedCarrier), ∀ x : Fin n → BananaTaggedCarrier,
      ∃ t ∈ T, ∃ g : FirstOrderAut bananaFunctionalLanguage BananaTaggedCarrier, g • t = x := by
  obtain ⟨T, hT⟩ := bananaLimit_exists_finite_tagged_tuple_orbit_representatives n
  refine ⟨T, fun x => ?_⟩
  obtain ⟨t, ht, EL, ER, hpair, hacts⟩ := hT x
  let f := aut EL ER hpair
  refine ⟨t, ht, FirstOrderAut.ofEquiv f.symm, funext fun j => ?_⟩
  change f.symm (t j) = x j
  have hf : f (x j) = bananaLimitTaggedAct EL ER (x j) := by
    cases x j <;> rfl
  exact f.symm_apply_eq.mpr (hf.trans (hacts j)).symm

/-- Countable categoricity in the presentation with actual algebraic closure. -/
theorem categorical :
    Cardinal.Categorical Cardinal.aleph0
      (bananaFunctionalLanguage.completeTheory BananaTaggedCarrier) :=
  categorical_completeTheory_of_finite_tupleOrbitRepresentatives finite_tuple_orbit_representatives

instance countable_function_symbols :
    Countable (Σ n, bananaFunctionalLanguage.Functions n) := by
  change Countable (Σ n, BananaFunctionalSymbol n)
  let code : (Σ n, BananaFunctionalSymbol n) → Fin 3
    | ⟨_, .leftZero⟩ => 0
    | ⟨_, .rightZero⟩ => 1
    | ⟨_, .add⟩ => 2
  apply Function.Injective.countable (f := code)
  rintro ⟨_, f⟩ ⟨_, g⟩ h
  cases f <;> cases g <;> first | rfl | simp [code] at h

/-- The explicit model is the Fraïssé limit of its genuine functional age. -/
theorem limit_isFraisseLimit :
    Language.IsFraisseLimit (bananaFunctionalLanguage.age BananaTaggedCarrier)
      BananaTaggedCarrier :=
  ⟨limit_ultrahomogeneous, rfl⟩

end BananaFunctional
end SuccessorTree.NonPrecompact
