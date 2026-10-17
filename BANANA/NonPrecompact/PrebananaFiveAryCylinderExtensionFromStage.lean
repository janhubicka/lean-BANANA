import BANANA.NonPrecompact.PrebananaCountableMarkedBooleanModel
import BANANA.NonPrecompact.PrebananaFiveAryFiniteExtensionTheorem
import BANANA.NonPrecompact.PrebananaFiveAryCylinderTowerCompatibility

/-!
# Extend finite marked Boolean embeddings into the cylinder limit

This module isolates the final extension step once the prescribed
finite base embedding in the countable cylinder algebra has been
factored through one finite five-ary stage.

Apply the verified unconditional marked finite-extension theorem
to that stage factor. Compose the resulting finite-stage embedding
with the genuine marked stage embedding into the cylinder limit.
Exact commutation follows from the already verified cylinder/tower
compatibility theorem.

The required factorisation of arbitrary finite marked embeddings
is now verified separately in `PrebananaFiveAryCylinderFiniteEmbeddingFactor`.
That theorem will be combined with this lemma in the unconditional
extension-property interface. No ultrahomogeneity assumption occurs here.
-/

namespace SuccessorTree.NonPrecompact

/-- Given a specified finite-stage factor of an embedding of the
finite base into the countable cylinder model, every finite marked
extension of that base can be embedded into the cylinder model,
commuting with the originally prescribed base embedding. -/
theorem prebananaCylinder_extension_of_stageFactor
    (A B : PrebananaFiniteBooleanModel)
    (f : PrebananaFiniteBooleanEmbedding A B)
    (e : PrebananaFiniteToCountableEmbedding
      A prebananaCylinderCountableModel)
    (n : ℕ)
    (g : PrebananaFiniteBooleanEmbedding A
      (prebananaFiveAryBooleanStage n))
    (hfactor : ∀ x : A.carrier,
      prebananaFiveAryCylinderStageEmbedding n (g.hom x) =
        e.hom x) :
    ∃ h : PrebananaFiniteToCountableEmbedding
        B prebananaCylinderCountableModel,
      ∀ x : A.carrier, h.hom (f.hom x) = e.hom x := by
  obtain ⟨k, hstage, hcomm⟩ :=
    prebananaFiveAry_finiteExtension_exists A B n f g
  let j : PrebananaFiniteToCountableEmbedding
      (prebananaFiveAryBooleanStage (n + k))
      prebananaCylinderCountableModel :=
    prebananaCylinderCountableStageEmbedding (n + k)
  let h : PrebananaFiniteToCountableEmbedding
      B prebananaCylinderCountableModel := {
    hom := j.hom.comp hstage.hom
    injective := by
      intro x y hxy
      exact hstage.injective (j.injective hxy)
    preserves_μ := by
      intro x
      calc
        prebananaCylinderCountableModel.μ
          ((j.hom.comp hstage.hom) x) =
            (prebananaFiveAryBooleanStage (n + k)).μ (hstage.hom x) :=
          j.preserves_μ (hstage.hom x)
        _ = B.μ x := hstage.preserves_μ x
  }
  refine ⟨h, ?_⟩
  intro x
  change j.hom (hstage.hom (f.hom x)) = e.hom x
  have hstep :
      j.hom
        ((prebananaExplicitFiveAryTower.iterFrom n k).hom (g.hom x)) =
      prebananaFiveAryCylinderStageEmbedding n (g.hom x) := by
    change prebananaFiveAryCylinderStageEmbedding (n + k)
      ((prebananaExplicitFiveAryTower.iterFrom n k).hom (g.hom x)) =
      prebananaFiveAryCylinderStageEmbedding n (g.hom x)
    exact prebananaFiveAryCylinderStageEmbedding_iter n k (g.hom x)
  exact ((congrArg j.hom (hcomm x)).trans hstep).trans (hfactor x)

end SuccessorTree.NonPrecompact
