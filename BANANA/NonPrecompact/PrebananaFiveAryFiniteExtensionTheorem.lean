import BANANA.NonPrecompact.PrebananaFiniteStageAtomPartition
import BANANA.NonPrecompact.PrebananaFiveAryAbstractExtensionFromPartitions

/-!
# Arbitrary finite-extension property for the explicit pre-BANANA tower

For any finite marked Boolean algebras A and B and any pair of genuine
marked unital embeddings A ↪ B and A ↪ stage(n), the embedding of the
base in the explicit five-ary tower extends to a copy of B at a later
finite stage. The depth is explicitly the number of atoms of B.

The proof uses the complete atom partition equations, including
equality of the actual Boolean-element maps, and the independently
verified marked allocation over each source atom. No Fraïssé limit
or homogeneity assumption is used.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- The full finite extension property at explicit depth |At(B)|,
for arbitrary genuine finite marked Boolean algebra embeddings. -/
theorem prebananaFiveAry_finiteExtension_ofEmbeddings
    (A B : PrebananaFiniteBooleanModel) (n : ℕ)
    (f : PrebananaFiniteBooleanEmbedding A B)
    (e : PrebananaFiniteBooleanEmbedding
      A (prebananaFiveAryBooleanStage n)) :
    ∃ g : PrebananaFiniteBooleanEmbedding B
        (prebananaFiveAryBooleanStage
          (n + Fintype.card (PrebananaAbstractAtoms B.carrier))),
      ∀ x : A.carrier,
        g.hom (f.hom x) =
          (prebananaExplicitFiveAryTower.iterFrom n
            (Fintype.card (PrebananaAbstractAtoms B.carrier))).hom
              (e.hom x) := by
  obtain ⟨source, target, hsource, htarget, hlocal,
      hsourceMap, htargetMap⟩ :=
    prebananaFiniteExtension_exists_compatibleAtomPartitions A B n f e
  exact prebananaFiveAry_abstractExtensionFromPartitions
    A B n f e source target hsource htarget hlocal
      hsourceMap htargetMap

/-- The usual existential-depth formulation of the finite-extension
property, with no auxiliary assumptions or atom coordinates exposed. -/
theorem prebananaFiveAry_finiteExtension_exists
    (A B : PrebananaFiniteBooleanModel) (n : ℕ)
    (f : PrebananaFiniteBooleanEmbedding A B)
    (e : PrebananaFiniteBooleanEmbedding
      A (prebananaFiveAryBooleanStage n)) :
    ∃ k : ℕ,
      ∃ g : PrebananaFiniteBooleanEmbedding B
          (prebananaFiveAryBooleanStage (n + k)),
        ∀ x : A.carrier,
          g.hom (f.hom x) =
            (prebananaExplicitFiveAryTower.iterFrom n k).hom
              (e.hom x) := by
  obtain ⟨g, hg⟩ :=
    prebananaFiveAry_finiteExtension_ofEmbeddings A B n f e
  exact ⟨Fintype.card (PrebananaAbstractAtoms B.carrier), g, hg⟩

end SuccessorTree.NonPrecompact
