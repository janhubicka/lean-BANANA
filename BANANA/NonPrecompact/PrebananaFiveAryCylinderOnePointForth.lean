import BANANA.NonPrecompact.PrebananaCountableOnePointExtension
import BANANA.NonPrecompact.PrebananaFiveAryCylinderFiniteAmbient
import BANANA.NonPrecompact.PrebananaFiveAryCylinderExtensionProperty

/-!
# Verified finite one-point extension in the explicit pre-BANANA cylinders

The generic one-point forth theorem needs only finite Boolean
ambients and the extension property for finite marked Boolean
embeddings. Both are available for the explicit countable
five-ary cylinder model.

This module supplies the genuine finite-domain forth step used
in back-and-forth. It deliberately does not identify this step
with a global automorphism or assume ultrahomogeneity.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- The cylinder algebra satisfies the finite-ambient-subalgebra
hypothesis needed for the abstract one-point forth theorem. -/
theorem prebananaCylinder_hasFiniteAmbients :
    prebananaCylinderCountableModel.HasFiniteAmbients := by
  classical
  intro xs
  obtain ⟨S, hfinite, hmem⟩ :=
    prebananaFiveAryCylinder_finiteAmbient
      (fun y : xs => (y : PrebananaFiveAryCylinderLimitCarrier))
  refine ⟨S, hfinite, ?_⟩
  intro x hx
  exact hmem ⟨x, hx⟩

/-- The cylinder algebra has the full marked finite-extension
property, with arbitrary finite diagrams and prescribed embeddings
of their bases. -/
theorem prebananaCylinder_hasFiniteExtensionProperty :
    prebananaCylinderCountableModel.HasFiniteExtensionProperty := by
  intro A B f e
  exact prebananaCylinder_finiteExtensionProperty A B f e

/-- Extend a finite marked partial map over a prescribed new
element in the first (source) copy of the cylinder algebra.
The second copy receives a compatible marked embedding of the
whole enlarged finite source structure. -/
theorem prebananaCylinder_onePointForth
    (A : PrebananaFiniteBooleanModel)
    (j e : PrebananaFiniteToCountableEmbedding
      A prebananaCylinderCountableModel)
    (x : PrebananaFiveAryCylinderLimitCarrier) :
    ∃ B : PrebananaFiniteBooleanModel,
      ∃ f : PrebananaFiniteBooleanEmbedding A B,
      ∃ i h : PrebananaFiniteToCountableEmbedding
        B prebananaCylinderCountableModel,
      ∃ y : B.carrier,
        i.hom y = x ∧
        (∀ a : A.carrier, i.hom (f.hom a) = j.hom a) ∧
        (∀ a : A.carrier, h.hom (f.hom a) = e.hom a) := by
  exact prebananaCylinderCountableModel.onePointForth
    prebananaCylinder_hasFiniteAmbients
    prebananaCylinder_hasFiniteExtensionProperty
    A j e x

end SuccessorTree.NonPrecompact
