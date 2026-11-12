import BANANA.NonPrecompact.BananaMatrixAutGroup
import BANANA.NonPrecompact.CoherentEppaPackage

/-!
# A group homomorphism for an aligned embedded perfect completion

The earlier ambient-action theorem supplies self-embeddings and their
identity/composition laws. Finite injective self-maps are bijective, so we
can now package those very same actions in the concrete automorphism group.
This is the homomorphism needed for representative transport in one common
perfect witness. The aligned-completion existence hypotheses remain visible.
-/

namespace SuccessorTree.NonPrecompact

/-- Finite injective self-embeddings are genuine two-sorted automorphisms. -/
noncomputable def BananaMatrixEmbedding.toAutGroup
    {l r : ℕ} {A : BananaMatrixStructure l r} (e : BananaMatrixEmbedding A A) :
    BananaMatrixAutGroup A := by
  let f := LinearEquiv.ofBijective e.left
    ⟨e.left_injective, Finite.injective_iff_surjective.mp e.left_injective⟩
  let g := LinearEquiv.ofBijective e.right
    ⟨e.right_injective, Finite.injective_iff_surjective.mp e.right_injective⟩
  exact ⟨⟨f, g⟩, e.pairing_apply⟩

/-- The conversion does not change the left action. -/
@[simp] theorem BananaMatrixEmbedding.toAutGroup_left_apply
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (e : BananaMatrixEmbedding A A) (x : Fin l → F2) :
    e.toAutGroup.1.1 x = e.left x := rfl

/-- The conversion does not change the right action. -/
@[simp] theorem BananaMatrixEmbedding.toAutGroup_right_apply
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (e : BananaMatrixEmbedding A A) (y : Fin r → F2) :
    e.toAutGroup.1.2 y = e.right y := rfl

open BananaMatrixStructure

/-- The fixed embedded-completion action as a genuine group homomorphism. -/
noncomputable def bananaMatrixEmbeddedCompletionActionHom
    {l r k : ℕ} (A : BananaMatrixStructure l r)
    (E : BananaMatrixEmbedding (perfectBanana (l + r))
      (perfectBanana ((l + r) + k))) :
    BananaMatrixAutGroup A →* BananaMatrixAutGroup (perfectBanana ((l + r) + k)) where
  toFun f := (embeddedCompletionAmbientAutomorphism E f.1.1 f.1.2).toAutGroup
  map_one' := by
    apply Subtype.ext
    apply Prod.ext
    · apply LinearEquiv.ext
      intro x
      change (embeddedCompletionAmbientAutomorphism E
        (LinearEquiv.refl F2 (Fin l → F2))
        (LinearEquiv.refl F2 (Fin r → F2))).left x = x
      exact congrArg
        (fun h : (Fin ((l + r) + k) → F2) →ₗ[F2]
          (Fin ((l + r) + k) → F2) => h x)
        (embeddedCompletionAmbientAutomorphism_refl_left E)
    · apply LinearEquiv.ext
      intro y
      change (embeddedCompletionAmbientAutomorphism E
        (LinearEquiv.refl F2 (Fin l → F2))
        (LinearEquiv.refl F2 (Fin r → F2))).right y = y
      exact congrArg
        (fun h : (Fin ((l + r) + k) → F2) →ₗ[F2]
          (Fin ((l + r) + k) → F2) => h y)
        (embeddedCompletionAmbientAutomorphism_refl_right E)
  map_mul' := by
    intro f g
    apply Subtype.ext
    apply Prod.ext
    · apply LinearEquiv.ext
      intro x
      change (embeddedCompletionAmbientAutomorphism E
        (g.1.1.trans f.1.1) (g.1.2.trans f.1.2)).left x =
          (embeddedCompletionAmbientAutomorphism E f.1.1 f.1.2).left
            ((embeddedCompletionAmbientAutomorphism E g.1.1 g.1.2).left x)
      exact congrArg
        (fun h : (Fin ((l + r) + k) → F2) →ₗ[F2]
          (Fin ((l + r) + k) → F2) => h x)
        (embeddedCompletionAmbientAutomorphism_comp_left E
          g.1.1 f.1.1 g.1.2 f.1.2)
    · apply LinearEquiv.ext
      intro y
      change (embeddedCompletionAmbientAutomorphism E
        (g.1.1.trans f.1.1) (g.1.2.trans f.1.2)).right y =
          (embeddedCompletionAmbientAutomorphism E f.1.1 f.1.2).right
            ((embeddedCompletionAmbientAutomorphism E g.1.1 g.1.2).right y)
      exact congrArg
        (fun h : (Fin ((l + r) + k) → F2) →ₗ[F2]
          (Fin ((l + r) + k) → F2) => h y)
        (embeddedCompletionAmbientAutomorphism_comp_right E
          g.1.1 f.1.1 g.1.2 f.1.2)

/-- An aligned group homomorphism extends every representative automorphism
on both sorts. The same homomorphism works for all of them simultaneously. -/
theorem exists_bananaMatrixAlignedCompletionHom
    {l r k : ℕ} (A : BananaMatrixStructure l r)
    (j : BananaMatrixEmbedding A (perfectBanana ((l + r) + k)))
    (E₀ : BananaMatrixEmbedding (perfectBanana (l + r))
      (perfectBanana ((l + r) + k))) :
    ∃ rho : BananaMatrixAutGroup A →*
        BananaMatrixAutGroup (perfectBanana ((l + r) + k)),
      ∀ f : BananaMatrixAutGroup A,
        (∀ x, (rho f).1.1 (j.left x) = j.left (f.1.1 x)) ∧
        (∀ y, (rho f).1.2 (j.right y) = j.right (f.1.2 y)) := by
  obtain ⟨E, _, _, hExt, _, _, _, _⟩ := A.exists_alignedCoherentAmbientAction j E₀
  refine ⟨bananaMatrixEmbeddedCompletionActionHom A E, ?_⟩
  intro f
  exact hExt f.1.1 f.1.2 f.pairing_apply

end SuccessorTree.NonPrecompact
