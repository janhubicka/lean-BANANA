import BANANA.NonPrecompact.BananaLimitExtremelyAmenableDegree
import BANANA.NonPrecompact.BananaDirectSumCanonical

/-!
# Colours invariant under a finite parameter stabiliser

Inside the explicit countable BANANA model, a target can be chosen in a
zero-cross-pairing direct sum with a finite block containing the parameters.
The pointwise stabiliser of those parameters is then transitive on the
images of all embeddings of the source within that target.
-/

namespace SuccessorTree.NonPrecompact

private theorem limitEmbedding_eq_of_sorts {l r : ℕ} {A : BananaMatrixStructure l r}
    {e f : BananaMatrixEmbeddingToLimit A}
    (hL : ∀ x, e.left x = f.left x) (hR : ∀ y, e.right y = f.right y) : e = f := by
  have hl : e.left = f.left := LinearMap.ext hL
  have hr : e.right = f.right := LinearMap.ext hR
  cases e
  cases f
  cases hl
  cases hr
  rfl

/-- Every finite target has a copy in the concrete limit on which any two
source embeddings are conjugate by an automorphism fixing the given finite
parameter sets pointwise. -/
theorem exists_bananaLimit_target_with_parameterStabilizer_transitive
    {lA rA lB rB : ℕ} (A : BananaMatrixStructure lA rA)
    (B : BananaMatrixStructure lB rB) (leftParams rightParams : Finset BananaLimitVector) :
    ∃ b : BananaMatrixEmbeddingToLimit B,
      ∀ f₀ f₁ : BananaMatrixEmbedding A B, ∃ g : BananaLimitAutomorphism,
        (∀ x ∈ leftParams, g.val.1 x = x) ∧
        (∀ y ∈ rightParams, g.val.2 y = y) ∧
        g • b.comp f₀ = b.comp f₁ := by
  let S := bananaLimitCommonSupport leftParams rightParams
  let P := perfectBanana S.card
  let p := bananaLimitBlockStandardEmbedding S
  obtain ⟨e⟩ := (bananaDirectSum P B).embeds_in_explicit_limit
  obtain ⟨g₀, hg₀⟩ := (e.comp (P.directSumInlEmbedding B)).exists_automorphism_smul_eq p
  let E := g₀ • e
  let b := E.comp (P.directSumInrEmbedding B)
  have hpL (x : Fin S.card → F2) : E.left ((P.directSumInlEmbedding B).left x) = p.left x :=
    congrArg (fun f : BananaMatrixEmbeddingToLimit P => f.left x) hg₀
  have hpR (y : Fin S.card → F2) : E.right ((P.directSumInlEmbedding B).right y) = p.right y :=
    congrArg (fun f : BananaMatrixEmbeddingToLimit P => f.right y) hg₀
  refine ⟨b, fun f₀ f₁ => ?_⟩
  let idP : BananaMatrixEmbedding P P :=
    ⟨LinearMap.id, LinearMap.id, Function.injective_id, Function.injective_id, fun _ _ => rfl⟩
  let d (f : BananaMatrixEmbedding A B) :=
    BananaMatrixStructure.directSumEmbedding P A idP f
  have hinlL (f : BananaMatrixEmbedding A B) (x : Fin S.card → F2) :
      (E.comp (d f)).left ((P.directSumInlEmbedding A).left x) = p.left x := by
    change E.left (((d f).left.comp (P.directSumInlEmbedding A).left) x) = p.left x
    have h := LinearMap.congr_fun (BananaMatrixStructure.directSum_natural_inl_left
      P A idP f) x
    exact (congrArg E.left h).trans (hpL x)
  have hinlR (f : BananaMatrixEmbedding A B) (y : Fin S.card → F2) :
      (E.comp (d f)).right ((P.directSumInlEmbedding A).right y) = p.right y := by
    change E.right (((d f).right.comp (P.directSumInlEmbedding A).right) y) = p.right y
    have h := LinearMap.congr_fun (BananaMatrixStructure.directSum_natural_inl_right
      P A idP f) y
    exact (congrArg E.right h).trans (hpR y)
  have hinrL (f : BananaMatrixEmbedding A B) (x : Fin lA → F2) :
      (E.comp (d f)).left ((P.directSumInrEmbedding A).left x) = (b.comp f).left x := by
    exact congrArg E.left (LinearMap.congr_fun (BananaMatrixStructure.directSum_natural_inr_left
      P A idP f) x)
  have hinrR (f : BananaMatrixEmbedding A B) (y : Fin rA → F2) :
      (E.comp (d f)).right ((P.directSumInrEmbedding A).right y) = (b.comp f).right y := by
    exact congrArg E.right (LinearMap.congr_fun (BananaMatrixStructure.directSum_natural_inr_right
      P A idP f) y)
  obtain ⟨g, hg⟩ := (E.comp (d f₀)).exists_automorphism_smul_eq (E.comp (d f₁))
  have hL (x : Fin (S.card + lA) → F2) :
      g.val.1 ((E.comp (d f₀)).left x) = (E.comp (d f₁)).left x :=
    congrArg (fun f : BananaMatrixEmbeddingToLimit (bananaDirectSum P A) => f.left x) hg
  have hR (y : Fin (S.card + rA) → F2) :
      g.val.2 ((E.comp (d f₀)).right y) = (E.comp (d f₁)).right y :=
    congrArg (fun f : BananaMatrixEmbeddingToLimit (bananaDirectSum P A) => f.right y) hg
  refine ⟨g, ?_, ?_, limitEmbedding_eq_of_sorts ?_ ?_⟩
  · intro x hx
    let v : bananaLimitBlock S :=
      ⟨x, bananaLimit_left_mem_common_block leftParams rightParams x hx⟩
    let a := (bananaLimitBlockStandardEquiv S).symm v
    have ha : p.left a = x := congrArg Subtype.val
      ((bananaLimitBlockStandardEquiv S).apply_symm_apply v)
    have key := hL ((P.directSumInlEmbedding A).left a)
    rwa [hinlL f₀, hinlL f₁, ha] at key
  · intro y hy
    let v : bananaLimitBlock S :=
      ⟨y, bananaLimit_right_mem_common_block leftParams rightParams y hy⟩
    let a := (bananaLimitBlockStandardEquiv S).symm v
    have ha : p.right a = y := congrArg Subtype.val
      ((bananaLimitBlockStandardEquiv S).apply_symm_apply v)
    have key := hR ((P.directSumInlEmbedding A).right a)
    rwa [hinlR f₀, hinlR f₁, ha] at key
  · intro x
    have key := hL ((P.directSumInrEmbedding A).left x)
    rwa [hinrL f₀, hinrL f₁] at key
  · intro y
    have key := hR ((P.directSumInrEmbedding A).right y)
    rwa [hinrR f₀, hinrR f₁] at key

/-- A colouring invariant under a finite parameter stabiliser in the
explicit countable BANANA model has a monochromatic copy of every target. -/
theorem exists_bananaLimit_monochromatic_target_of_finite_parameters
    {lA rA lB rB : ℕ} {A : BananaMatrixStructure lA rA} (B : BananaMatrixStructure lB rB)
    (leftParams rightParams : Finset BananaLimitVector)
    {Colour : Type*} (colour : BananaMatrixEmbeddingToLimit A → Colour)
    (hinvariant : ∀ (g : BananaLimitAutomorphism),
      (∀ x ∈ leftParams, g.val.1 x = x) → (∀ y ∈ rightParams, g.val.2 y = y) →
      ∀ f, colour (g • f) = colour f) :
    ∃ b : BananaMatrixEmbeddingToLimit B,
      ∀ f₀ f₁ : BananaMatrixEmbedding A B, colour (b.comp f₀) = colour (b.comp f₁) := by
  obtain ⟨b, hb⟩ :=
    exists_bananaLimit_target_with_parameterStabilizer_transitive A B leftParams rightParams
  refine ⟨b, fun f₀ f₁ => ?_⟩
  obtain ⟨g, hL, hR, he⟩ := hb f₀ f₁
  exact (hinvariant g hL hR (b.comp f₀)).symm.trans (congrArg colour he)

end SuccessorTree.NonPrecompact
