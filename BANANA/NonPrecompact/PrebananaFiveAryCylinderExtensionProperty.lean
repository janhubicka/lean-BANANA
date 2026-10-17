import BANANA.NonPrecompact.PrebananaFiveAryCylinderFiniteEmbeddingFactor
import BANANA.NonPrecompact.PrebananaFiveAryCylinderExtensionFromStage

/-!
# Finite extension property of the explicit countable pre-BANANA algebra

The finite extension theorem in the five-ary tower and finite-stage
factorisation of arbitrary embeddings into its cylinder algebra imply
the genuine extension property for the countable marked Boolean model.

There are no extra assumptions about presentations, split embeddings,
Fraïssé limits or ultrahomogeneity. The conclusion produces a marked
embedding of the whole finite target, commuting *on every element* of
the prescribed finite base.

This is the key extension property used in the separate back-and-forth
proof of ultrahomogeneity.
-/

namespace SuccessorTree.NonPrecompact

/-- Any marked embedding of finite A into the countable cylinder
algebra extends along any given marked embedding A ↪ B, with
an actual marked embedding B into the same countable algebra. -/
theorem prebananaCylinder_finiteExtensionProperty
    (A B : PrebananaFiniteBooleanModel)
    (f : PrebananaFiniteBooleanEmbedding A B)
    (e : PrebananaFiniteToCountableEmbedding
      A prebananaCylinderCountableModel) :
    ∃ h : PrebananaFiniteToCountableEmbedding
        B prebananaCylinderCountableModel,
      ∀ x : A.carrier, h.hom (f.hom x) = e.hom x := by
  obtain ⟨n, g, hfactor⟩ :=
    prebananaFiveAryCylinder_finiteEmbedding_factor
      A e.hom e.injective e.preserves_μ
  exact prebananaCylinder_extension_of_stageFactor
    A B f e n g hfactor

end SuccessorTree.NonPrecompact
