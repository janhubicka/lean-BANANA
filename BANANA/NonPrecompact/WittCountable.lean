import BANANA.NonPrecompact.WittAdjoinIsometry
import Mathlib.ModelTheory.Fraisse

/-!
# Isometry extension in countable alternating spaces

A vector space with a bilinear form is a first-order structure with the
vector-space operations and one binary relation per pairing value. Its
finitely generated substructures correspond to finite-dimensional subspaces.
The linear one-point extension gives mathlib's extension property, so its
back-and-forth theorem extends finite partial isometries to automorphisms.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

private inductive PairingFunction (K : Type*) : ℕ → Type _
  | zero : PairingFunction K 0
  | add : PairingFunction K 2
  | smul (a : K) : PairingFunction K 1

private inductive PairingRelation (K : Type*) : ℕ → Type _
  | pair (a : K) : PairingRelation K 2

private def pairingLanguage (K : Type*) : Language where
  Functions := PairingFunction K
  Relations := PairingRelation K

@[instance_reducible]
private def pairingStructure {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) : (pairingLanguage K).Structure V where
  funMap {n} f x := match f with
    | .zero => 0
    | .add => x 0 + x 1
    | .smul a => a • x 0
  RelMap {n} r x := match r with
    | .pair a => B (x 0) (x 1) = a

section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private abbrev asSubmodule (B : LinearMap.BilinForm K V)
    (S : @Language.Substructure (pairingLanguage K) V (pairingStructure B)) : Submodule K V := by
  letI := pairingStructure B
  exact {
    carrier := S.carrier
    zero_mem' := S.fun_mem (PairingFunction.zero : (pairingLanguage K).Functions 0)
      Fin.elim0 (fun i => Fin.elim0 i)
    add_mem' := by
      intro x y hx hy
      exact S.fun_mem (PairingFunction.add : (pairingLanguage K).Functions 2) ![x, y] (by
        intro i
        fin_cases i
        · exact hx
        · exact hy)
    smul_mem' := by
      intro a x hx
      exact S.fun_mem (PairingFunction.smul a : (pairingLanguage K).Functions 1)
        (fun _ => x) (fun _ => hx) }

private abbrev asSubstructure (B : LinearMap.BilinForm K V) (S : Submodule K V) :
    @Language.Substructure (pairingLanguage K) V (pairingStructure B) := by
  letI := pairingStructure B
  exact {
    carrier := S
    fun_mem := by
      intro n f x hx
      cases f with
      | zero => exact S.zero_mem
      | add => exact S.add_mem (hx 0) (hx 1)
      | smul a => exact S.smul_mem a (hx 0) }

private theorem closure_eq_span (B : LinearMap.BilinForm K V) (s : Set V) :
    letI := pairingStructure B
    Language.Substructure.closure (pairingLanguage K) s =
      asSubstructure B (Submodule.span K s) := by
  let _ := pairingStructure B
  apply le_antisymm
  · exact Language.Substructure.closure_le.mpr (Submodule.subset_span (R := K))
  · have h : Submodule.span K s ≤
      asSubmodule B (Language.Substructure.closure (pairingLanguage K) s) :=
      Submodule.span_le.mpr Language.Substructure.subset_closure
    exact h

private def embeddingLinearMap (B : LinearMap.BilinForm K V)
    (S : @Language.Substructure (pairingLanguage K) V (pairingStructure B))
    (f : letI := pairingStructure B; S ↪[pairingLanguage K] V) : asSubmodule B S →ₗ[K] V := by
  letI := pairingStructure B
  exact {
    toFun := f
    map_add' := fun x y => f.map_fun (PairingFunction.add : (pairingLanguage K).Functions 2) ![x, y]
    map_smul' := fun a x =>
      f.map_fun (PairingFunction.smul a : (pairingLanguage K).Functions 1) (fun _ => x) }

private theorem embeddingLinearMap_pairing (B : LinearMap.BilinForm K V)
    (S : @Language.Substructure (pairingLanguage K) V (pairingStructure B))
    (f : letI := pairingStructure B; S ↪[pairingLanguage K] V) (x y : asSubmodule B S) :
    B (embeddingLinearMap B S f x) (embeddingLinearMap B S f y) = B x y := by
  let _ := pairingStructure B
  exact (f.map_rel (PairingRelation.pair (B x y) : (pairingLanguage K).Relations 2) ![x, y]).mpr rfl

private def isometryEmbedding (B : LinearMap.BilinForm K V) (S : Submodule K V)
    (f : S →ₗ[K] V) (hf : Function.Injective f) (hiso : ∀ u v : S, B (f u) (f v) = B u v) :
    letI := pairingStructure B
    asSubstructure B S ↪[pairingLanguage K] V := by
  letI := pairingStructure B
  exact {
    toFun := f
    inj' := hf
    map_fun' := by
      intro n g x
      cases g with
      | zero => exact f.map_zero
      | add => exact f.map_add _ _
      | smul a => exact f.map_smul a _
    map_rel' := by
      intro n r x
      cases r with
      | pair a =>
        change B (f (x 0)) (f (x 1)) = a ↔ B (x 0) (x 1) = a
        rw [hiso] }

private theorem finiteDimensional_of_fg (B : LinearMap.BilinForm K V)
    (S : @Language.Substructure (pairingLanguage K) V (pairingStructure B))
    (hS : letI := pairingStructure B; S.FG) : FiniteDimensional K (asSubmodule B S) := by
  let _ := pairingStructure B
  obtain ⟨s, hs, rfl⟩ := Language.Substructure.fg_def.mp hS
  rw [closure_eq_span B]
  exact FiniteDimensional.span_of_finite K hs

private theorem adjoin_eq_sup_closure_singleton (B : LinearMap.BilinForm K V)
    (S : @Language.Substructure (pairingLanguage K) V (pairingStructure B)) (x : V) :
    letI := pairingStructure B
    asSubstructure B (asSubmodule B S ⊔ K ∙ x) =
      S ⊔ Language.Substructure.closure (pairingLanguage K) {x} := by
  let _ := pairingStructure B
  apply le_antisymm
  · change asSubmodule B S ⊔ K ∙ x ≤ asSubmodule B (S ⊔ Language.Substructure.closure _ {x})
    apply sup_le
    · exact (show S ≤ S ⊔ Language.Substructure.closure _ {x} from le_sup_left)
    · apply Submodule.span_le.mpr
      have h : Language.Substructure.closure _ {x} ≤
          S ⊔ Language.Substructure.closure _ {x} := le_sup_right
      exact Language.Substructure.subset_closure.trans h
  · apply sup_le
    · exact (show asSubmodule B S ≤ asSubmodule B S ⊔ K ∙ x from le_sup_left)
    · apply Language.Substructure.closure_le.mpr
      intro y hy
      have hyx := Set.mem_singleton_iff.mp hy
      subst y
      exact (show K ∙ x ≤ asSubmodule B S ⊔ K ∙ x from le_sup_right)
        (Submodule.mem_span_singleton_self x)

private theorem pairingLanguage_isExtensionPair (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hinf : ¬ FiniteDimensional K V) :
    letI := pairingStructure B
    (pairingLanguage K).IsExtensionPair V V := by
  let _ := pairingStructure B
  rintro ⟨f, hfg⟩ x
  by_cases hx : x ∈ f.dom
  · exact ⟨⟨f, hfg⟩, hx, le_rfl⟩
  let S := asSubmodule B f.dom
  let F := embeddingLinearMap B f.dom f.toEmbedding
  let _ : FiniteDimensional K S := finiteDimensional_of_fg B f.dom hfg
  obtain ⟨G, hGinj, hGiso, hG⟩ := exists_wittOnePointIsometry
    B B hB hB hnd hinf S F f.toEmbedding.injective
    (embeddingLinearMap_pairing B f.dom f.toEmbedding) x hx
  let T := asSubstructure B (S ⊔ K ∙ x)
  have hTfg : T.FG := by
    change (asSubstructure B (asSubmodule B f.dom ⊔ K ∙ x)).FG
    rw [adjoin_eq_sup_closure_singleton B]
    exact hfg.sup (Language.Substructure.fg_closure_singleton x)
  let g : T ↪[pairingLanguage K] V := isometryEmbedding B _ G hGinj hGiso
  have hST : f.dom ≤ T := (show S ≤ S ⊔ K ∙ x from le_sup_left)
  have hxT : x ∈ T := (show K ∙ x ≤ S ⊔ K ∙ x from le_sup_right)
    (Submodule.mem_span_singleton_self x)
  refine ⟨⟨⟨T, g.toHom.range, g.equivRange⟩, hTfg⟩, hxT, ⟨hST, ?_⟩⟩
  ext u
  exact hG u

/-- In a countable infinite-dimensional nondegenerate alternating space,
any isometric injection from a finite-dimensional subspace extends to a
linear isometric automorphism of the space. -/
theorem exists_wittCountableIsometry [Countable V]
    (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hinf : ¬ FiniteDimensional K V) (S : Submodule K V) [FiniteDimensional K S]
    (f : S →ₗ[K] V) (hf : Function.Injective f)
    (hiso : ∀ u v : S, B (f u) (f v) = B u v) :
    ∃ g : V ≃ₗ[K] V, (∀ u v : V, B (g u) (g v) = B u v) ∧ ∀ u : S, g u = f u := by
  let _ := pairingStructure B
  have hhom : (pairingLanguage K).IsUltrahomogeneous V :=
    (Language.isUltrahomogeneous_iff_IsExtensionPair (L := pairingLanguage K)
      (Language.Structure.cg_of_countable (L := pairingLanguage K) (M := V))).mpr
      (pairingLanguage_isExtensionPair B hB hnd hinf)
  let T := asSubstructure B S
  have hTfg : T.FG := by
    obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp (Module.Finite.iff_fg.mp
      (inferInstance : FiniteDimensional K S))
    exact Language.Substructure.fg_def.mpr ⟨s, hs, (closure_eq_span B s).trans (congrArg _ hspan)⟩
  obtain ⟨g, hg⟩ := hhom T hTfg (isometryEmbedding B S f hf hiso)
  let gₗ : V ≃ₗ[K] V := {
    g.toEquiv with
    map_add' := fun u v => g.map_fun (PairingFunction.add : (pairingLanguage K).Functions 2) ![u, v]
    map_smul' := fun a u =>
      g.map_fun (PairingFunction.smul a : (pairingLanguage K).Functions 1) (fun _ => u) }
  refine ⟨gₗ, ?_, ?_⟩
  · intro u v
    exact (g.map_rel (PairingRelation.pair (B u v) : (pairingLanguage K).Relations 2)
      ![u, v]).mpr rfl
  · intro u
    exact (DFunLike.congr_fun hg u).symm

end
end SuccessorTree.NonPrecompact
