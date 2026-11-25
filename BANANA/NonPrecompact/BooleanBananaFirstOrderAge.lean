import BANANA.NonPrecompact.BooleanBananaFirstOrderCategoricity
import BANANA.NonPrecompact.FirstOrderFunctionalRamseyAge
import BANANA.NonPrecompact.PrebananaFiveAryCylinderFiniteAge
import BANANA.NonPrecompact.PrebananaFiniteBooleanModelStrongAP

/-!
# The functional first-order age of Boolean–BANANA

The Boolean operations are actual function symbols. Thus the substructures of
the cylinder model are exactly the Boolean subalgebras, with the inherited
parity marking. We transport the existing native strong amalgamation and
homogeneity theorems to the first-order age.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open FirstOrder CategoryTheory
open scoped Classical FirstOrder

local notation "M" => PrebananaFiveAryCylinderLimitCarrier

/-- Translate a bounded lattice embedding preserving the mark into an
embedding of the actual first-order language. -/
def latticeEmbedding {A B : Type*} [BooleanAlgebra A] [BooleanAlgebra B]
    {μ : A → ZMod 2} {ν : B → ZMod 2}
    (f : BoundedLatticeHom A B) (hf : Function.Injective f) (hμ : ∀ a, ν (f a) = μ a) :
    @Language.Embedding markedBooleanLanguage A B (markedBooleanStructure A μ) (markedBooleanStructure B ν) := by
  letI := markedBooleanStructure A μ
  letI := markedBooleanStructure B ν
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro n g x
    change BooleanFunctions n at g
    cases g with
    | bot => exact map_bot f
    | top => exact map_top f
    | inf => exact map_inf f _ _
    | sup => exact map_sup f _ _
    | compl => exact map_compl' f _
  · intro n r x
    change MarkRelations n at r
    cases r
    change ν (f (x 0)) = 1 ↔ μ (x 0) = 1
    rw [hμ]

/-- Recover a bounded lattice homomorphism from a first-order embedding. -/
def embeddingLatticeHom {A B : Type*} [BooleanAlgebra A] [BooleanAlgebra B]
    {μ : A → ZMod 2} {ν : B → ZMod 2}
    (f : @Language.Embedding markedBooleanLanguage A B (markedBooleanStructure A μ) (markedBooleanStructure B ν)) :
    BoundedLatticeHom A B := by
  letI := markedBooleanStructure A μ
  letI := markedBooleanStructure B ν
  exact {
    toFun := f
    map_bot' := f.map_fun' (n := 0) BooleanFunctions.bot Fin.elim0
    map_top' := f.map_fun' (n := 0) BooleanFunctions.top Fin.elim0
    map_inf' a b := f.map_fun' (n := 2) BooleanFunctions.inf ![a, b]
    map_sup' a b := f.map_fun' (n := 2) BooleanFunctions.sup ![a, b] }

/-- A reflected unary mark predicate determines the whole binary marking. -/
theorem embedding_preserves_mark {A B : Type*} [BooleanAlgebra A] [BooleanAlgebra B]
    {μ : A → ZMod 2} {ν : B → ZMod 2}
    (f : @Language.Embedding markedBooleanLanguage A B (markedBooleanStructure A μ) (markedBooleanStructure B ν))
    (a : A) : ν (@Language.Embedding.toEmbedding markedBooleanLanguage A B
      (markedBooleanStructure A μ) (markedBooleanStructure B ν) f a) = μ a := by
  let _ := markedBooleanStructure A μ
  let _ := markedBooleanStructure B ν
  change ν (f a) = μ a
  have hm : ν (f a) = 1 ↔ μ a = 1 := f.map_rel' (n := 1) MarkRelations.marked (fun _ => a)
  have h01 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h01 (ν (f a)) with h | h <;> rcases h01 (μ a) with k | k <;> simp_all

/-- A substructure in the functional language is a Boolean subalgebra
on the same carrier. -/
abbrev substructureBooleanSubalgebra {A : Type*} [BooleanAlgebra A] {μ : A → ZMod 2}
    (S : @Language.Substructure markedBooleanLanguage A (markedBooleanStructure A μ)) : BooleanSubalgebra A := by
  letI := markedBooleanStructure A μ
  exact {
    carrier := S
    bot_mem' := S.fun_mem (n := 0) BooleanFunctions.bot Fin.elim0 (fun i => Fin.elim0 i)
    infClosed' := by
      intro a ha b hb
      refine S.fun_mem (n := 2) BooleanFunctions.inf ![a, b] ?_
      intro i
      fin_cases i <;> assumption
    supClosed' := by
      intro a ha b hb
      refine S.fun_mem (n := 2) BooleanFunctions.sup ![a, b] ?_
      intro i
      fin_cases i <;> assumption
    compl_mem' ha := S.fun_mem (n := 1) BooleanFunctions.compl (fun _ => _) (fun _ => ha) }

/-- A Boolean subalgebra is closed under each function of the first-order
language. -/
abbrev booleanSubalgebraSubstructure {A : Type*} [BooleanAlgebra A] {μ : A → ZMod 2}
    (S : BooleanSubalgebra A) : @Language.Substructure markedBooleanLanguage A (markedBooleanStructure A μ) := by
  letI := markedBooleanStructure A μ
  refine ⟨S, ?_⟩
  intro n f x hx
  change BooleanFunctions n at f
  cases f with
  | bot => exact S.bot_mem
  | top => exact S.top_mem
  | inf => exact S.inf_mem (hx 0) (hx 1)
  | sup => exact S.sup_mem (hx 0) (hx 1)
  | compl => exact S.compl_mem (hx 0)

/-- The Boolean subalgebra and first-order substructure interpretations
induce exactly the same structure on the subtype. -/
theorem substructure_markedBooleanStructure {A : Type*} [BooleanAlgebra A] {μ : A → ZMod 2}
    (S : @Language.Substructure markedBooleanLanguage A (markedBooleanStructure A μ)) :
    @Language.Substructure.inducedStructure markedBooleanLanguage A (markedBooleanStructure A μ) S =
      markedBooleanStructure (substructureBooleanSubalgebra S) (fun x => μ x.val) := by
  apply Language.Structure.ext
  · funext n f x
    change BooleanFunctions n at f
    cases f <;> rfl
  · funext n r x
    change MarkRelations n at r
    cases r
    rfl

/-- Bundle a native finite marked Boolean model in the first-order language. -/
def firstOrderModel (A : PrebananaFiniteBooleanModel) : Bundled markedBooleanLanguage.Structure :=
  ⟨A.carrier, markedBooleanStructure A.carrier A.μ⟩

private noncomputable def finiteSubmodel (S : markedBooleanLanguage.Substructure M) [Finite S] :
    PrebananaFiniteBooleanModel := by
  letI : Fintype (substructureBooleanSubalgebra S) := Fintype.ofFinite S
  exact prebananaCylinder_finiteSubmodel (substructureBooleanSubalgebra S)

private theorem finiteSubmodel_structure (S : markedBooleanLanguage.Substructure M) [Finite S] :
    @Language.Substructure.inducedStructure markedBooleanLanguage M _ S =
      (firstOrderModel (finiteSubmodel S)).str :=
  substructure_markedBooleanStructure S

private noncomputable def finiteSubmodelEquiv (S : markedBooleanLanguage.Substructure M) [Finite S] :
    S ≃[markedBooleanLanguage] firstOrderModel (finiteSubmodel S) := by
  change @Language.Equiv markedBooleanLanguage S S
    (@Language.Substructure.inducedStructure markedBooleanLanguage M _ S)
    (firstOrderModel (finiteSubmodel S)).str
  rw [← finiteSubmodel_structure S]

/-- The concrete cylinder structure is locally finite in the functional
first-order language. -/
theorem cylinder_finitelyGeneratedSubstructure_finite
    (S : markedBooleanLanguage.Substructure M) (hS : S.FG) : Finite S := by
  obtain ⟨s, rfl⟩ := hS
  obtain ⟨A, hA, hmem⟩ := prebananaCylinder_hasFiniteAmbients_forHomogeneity s
  let subalgebra := booleanSubalgebraSubstructure (μ := prebananaFiveAryCylinderMark) A
  have h : Language.Substructure.closure markedBooleanLanguage (s : Set M) ≤ subalgebra :=
    Language.Substructure.closure_le.mpr hmem
  let inclusion (x : Language.Substructure.closure markedBooleanLanguage (s : Set M)) : A :=
    ⟨x.val, h x.property⟩
  exact Finite.of_injective inclusion (fun _ _ e =>
    Subtype.ext (congrArg (fun a : A => a.val) e))

/-- The actual cylinder age consists precisely of the first-order
presentations of native finite Boolean–BANANA models up to isomorphism. -/
theorem cylinder_mem_age_iff (A : Bundled markedBooleanLanguage.Structure) :
    A ∈ markedBooleanLanguage.age M ↔ ∃ B : PrebananaFiniteBooleanModel, Nonempty (A ≃[markedBooleanLanguage] firstOrderModel B) := by
  constructor
  · intro h
    let f := h.2.some
    let _ := cylinder_finitelyGeneratedSubstructure_finite
      f.toHom.range (h.1.range f.toHom)
    exact ⟨finiteSubmodel f.toHom.range, ⟨(finiteSubmodelEquiv f.toHom.range).comp f.equivRange⟩⟩
  · rintro ⟨B, ⟨e⟩⟩
    obtain ⟨f⟩ := prebananaCylinder_allFiniteModels_embed B
    let _ : Finite (firstOrderModel B) := inferInstanceAs (Finite B.carrier)
    have : Finite A := Finite.of_injective e e.injective
    let ee : firstOrderModel B ↪[markedBooleanLanguage] M :=
      latticeEmbedding (A := B.carrier) (B := M) f.hom f.injective f.preserves_μ
    exact ⟨Language.Structure.FG.of_finite, ⟨ee.comp e.toEmbedding⟩⟩

/-- The explicit cylinder limit is ultrahomogeneous in the actual functional
first-order language. -/
theorem cylinder_firstOrder_ultrahomogeneous : markedBooleanLanguage.IsUltrahomogeneous M := by
  intro S hS f
  have := cylinder_finitelyGeneratedSubstructure_finite S hS
  let B := finiteSubmodel S
  let e := (finiteSubmodelEquiv S).symm.toEmbedding
  let i : firstOrderModel B ↪[markedBooleanLanguage] M := S.subtype.comp e
  let j : firstOrderModel B ↪[markedBooleanLanguage] M := f.comp e
  let g (r : firstOrderModel B ↪[markedBooleanLanguage] M) : PrebananaFiniteToCountableEmbedding
      B prebananaCylinderCountableModel :=
    ⟨embeddingLatticeHom (A := B.carrier) (B := M) (μ := B.μ)
      (ν := prebananaFiveAryCylinderMark) r, r.injective,
      embedding_preserves_mark (A := B.carrier) (B := M) (μ := B.μ)
        (ν := prebananaFiveAryCylinderMark) r⟩
  obtain ⟨E, hμ, hE⟩ := prebananaCylinder_exists_global_marked_boolean_automorphism B (g i) (g j)
  use markedBooleanAutomorphism E hμ
  ext x
  have hx := hE ((finiteSubmodelEquiv S) x)
  change E (S.subtype (e ((finiteSubmodelEquiv S) x))) =
    f (e ((finiteSubmodelEquiv S) x)) at hx
  rw [Language.Equiv.coe_toEmbedding, Language.Equiv.symm_apply_apply] at hx
  exact hx.symm

/-- Strong amalgamation in the actual Mathlib age, for all first-order
embeddings and hence for their native marked Boolean counterparts. -/
theorem cylinder_firstOrderAge_strongAmalgamation :
    FirstOrderStrongAmalgamation (markedBooleanLanguage.age M) := by
  intro A C B f g hA hC hB
  obtain ⟨A', ⟨eA⟩⟩ := (cylinder_mem_age_iff A).mp hA
  obtain ⟨C', ⟨eC⟩⟩ := (cylinder_mem_age_iff C).mp hC
  obtain ⟨B', ⟨eB⟩⟩ := (cylinder_mem_age_iff B).mp hB
  let restrict {X Y : PrebananaFiniteBooleanModel}
      (e : firstOrderModel X ↪[markedBooleanLanguage] firstOrderModel Y) :
      PrebananaFiniteBooleanEmbedding X Y :=
    ⟨embeddingLatticeHom (A := X.carrier) (B := Y.carrier) (μ := X.μ) (ν := Y.μ) e,
      e.injective, embedding_preserves_mark (A := X.carrier) (B := Y.carrier)
        (μ := X.μ) (ν := Y.μ) e⟩
  let f' := restrict (eC.toEmbedding.comp (f.comp eA.symm.toEmbedding))
  let g' := restrict (eB.toEmbedding.comp (g.comp eA.symm.toEmbedding))
  obtain ⟨Q, j, k, hcomm, hinter⟩ :=
    prebananaFiniteBooleanModel_strongAmalgamation A' C' B' f' g'
  let j' : firstOrderModel C' ↪[markedBooleanLanguage] firstOrderModel Q :=
    latticeEmbedding (A := C'.carrier) (B := Q.carrier) j.hom j.injective j.preserves_μ
  let k' : firstOrderModel B' ↪[markedBooleanLanguage] firstOrderModel Q :=
    latticeEmbedding (A := B'.carrier) (B := Q.carrier) k.hom k.injective k.preserves_μ
  refine ⟨firstOrderModel Q, j'.comp eC.toEmbedding, k'.comp eB.toEmbedding,
    (cylinder_mem_age_iff _).mpr ⟨Q, ⟨Language.Equiv.refl _ _⟩⟩, ?_, ?_⟩
  · ext a
    have he := hcomm (eA a)
    change j.hom (eC (f (eA.symm (eA a)))) =
      k.hom (eB (g (eA.symm (eA a)))) at he
    rw [Language.Equiv.symm_apply_apply] at he
    exact he
  · intro b c he
    obtain ⟨a, -, ha⟩ := hinter (eC c) (eB b) he.symm
    exact ⟨eA.symm a, eB.injective ha⟩

/-- The represented class consists precisely of the finite marked Boolean
models, with all isomorphic presentations. -/
def firstOrderClass : Set (Bundled markedBooleanLanguage.Structure) :=
  {A | ∃ B : PrebananaFiniteBooleanModel, Nonempty (A ≃[markedBooleanLanguage] firstOrderModel B)}

instance : Countable (Σ n, markedBooleanLanguage.Functions n) := by
  change Countable (Σ n, BooleanFunctions n)
  let code : (Σ n, BooleanFunctions n) → Fin 5
    | ⟨_, .bot⟩ => 0
    | ⟨_, .top⟩ => 1
    | ⟨_, .inf⟩ => 2
    | ⟨_, .sup⟩ => 3
    | ⟨_, .compl⟩ => 4
  apply Function.Injective.countable (f := code)
  rintro ⟨_, f⟩ ⟨_, g⟩ h
  cases f <;> cases g <;> first | rfl | simp [code] at h

/-- The concrete cylinder is the Mathlib Fraïssé limit of the native
Boolean–BANANA finite class in its functional language. -/
theorem cylinder_isFraisseLimit : Language.IsFraisseLimit firstOrderClass M where
  ultrahomogeneous := cylinder_firstOrder_ultrahomogeneous
  age := Set.ext cylinder_mem_age_iff

/-- The actual Boolean–BANANA age has a reasonable, precompact Ramsey
expansion when arbitrary added function symbols are permitted. -/
theorem cylinder_exists_namedFunctionalRamseyAge :
    ∃ F : FiniteClosureFamily markedBooleanLanguage M, IsReasonablePrecompactRamseyAge F :=
  firstOrder_exists_namedFunctionalRamseyAge_of_oligomorphic
    cylinder_finitelyGeneratedSubstructure_finite
    cylinder_firstOrder_ultrahomogeneous
    cylinder_firstOrderAge_strongAmalgamation
    cylinderMarkedBoolean_finite_tupleOrbitQuotients

end SuccessorTree.NonPrecompact.BooleanBanana
