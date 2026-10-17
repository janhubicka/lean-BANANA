import BANANA.NonPrecompact.PrebananaFiniteBridgeGlobalAutomorphism
import BANANA.NonPrecompact.PrebananaFiveAryCylinderFiniteAmbient
import BANANA.NonPrecompact.PrebananaFiveAryCylinderExtensionProperty

/-!
# Ultrahomogeneity of the explicit countable pre-BANANA algebra

The countable cylinder Boolean algebra is locally finite, and
each finite marked embedding into it extends along every finite
marked extension. Hence the generic two-sided marked Boolean
back-and-forth theorem applies.

The conclusion is an actual Boolean order automorphism of the
concrete countable cylinder algebra that preserves the unary
F₂ marking and carries either chosen finite marked embedding
to the other pointwise. It does not rely on an abstract
Fraïssé limit or a model-theoretic existence axiom.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Every finite set of cylinder elements belongs to a finite
Boolean subalgebra, as required for generic marked back-and-forth. -/
theorem prebananaCylinder_hasFiniteAmbients_forHomogeneity :
    prebananaCylinderCountableModel.HasFiniteAmbients := by
  classical
  intro xs
  obtain ⟨S, hfinite, hmem⟩ :=
    prebananaFiveAryCylinder_finiteAmbient
      (fun y : xs => (y : PrebananaFiveAryCylinderLimitCarrier))
  refine ⟨S, hfinite, ?_⟩
  intro x hx
  exact hmem ⟨x, hx⟩

/-- The genuine extension property of the countable marked
cylinder model follows from the checked finite-extension
and finite-stage factorisation theorems. -/
theorem prebananaCylinder_hasFiniteExtensionProperty_forHomogeneity :
    prebananaCylinderCountableModel.HasFiniteExtensionProperty := by
  intro A B f e
  exact prebananaCylinder_finiteExtensionProperty A B f e

/-- Every two marked embeddings of an arbitrary finite pre-BANANA
structure into the explicit countable cylinder algebra are
conjugate by an actual Boolean automorphism preserving the
F₂ marking. This is the embedding formulation of ultrahomogeneity. -/
theorem prebananaCylinder_exists_global_marked_boolean_automorphism
    (A : PrebananaFiniteBooleanModel)
    (i j : PrebananaFiniteToCountableEmbedding
      A prebananaCylinderCountableModel) :
    ∃ E : PrebananaFiveAryCylinderLimitCarrier ≃o
        PrebananaFiveAryCylinderLimitCarrier,
      (∀ x : PrebananaFiveAryCylinderLimitCarrier,
        prebananaFiveAryCylinderMark (E x) =
          prebananaFiveAryCylinderMark x) ∧
      ∀ a : A.carrier, E (i.hom a) = j.hom a := by
  exact PrebananaFiniteBridge.exists_global_marked_automorphism
    prebananaCylinder_hasFiniteAmbients_forHomogeneity
    prebananaCylinder_hasFiniteExtensionProperty_forHomogeneity
    ⟨A, i, j⟩

end SuccessorTree.NonPrecompact
