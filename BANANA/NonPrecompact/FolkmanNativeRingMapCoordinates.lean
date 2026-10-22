import BANANA.NonPrecompact.FolkmanNativeRingAtomInverse
import BANANA.NonPrecompact.PrebananaAbstractBooleanEmbeddingMap

/-!
# Naturality of finite atom coordinates for native Boolean-ring maps

The finite atom code from a Boolean ring to the subsets of atoms of
its associated Boolean algebra intertwines an arbitrary non-unital
ring map with the corresponding atom-powerset map.

No injectivity or preservation of the ring unit is needed for this
naturality identity. Injectivity is needed only for the subsequent
partial-owner theorem, already proved separately.

This is the reusable interface for transporting all four embeddings
in a native two-sorted Folkman amalgamation diagram.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

-- The finite-carrier instance is needed in theorem *statements*:
-- prebananaAbstractPowersetMap elaborates its implicit Fintype arguments
-- before the proof begins.  Locality avoids changing other modules.
local instance folkmanAsBoolAlgFiniteForMap
    (γ : Type*) [Fintype γ] : Fintype (AsBoolAlg γ) :=
  Fintype.ofEquiv γ toBoolAlg

/-- Transport an arbitrary native non-unital Boolean-ring homomorphism
through the source and target atom-coordinate equivalences.

The result is exactly the existing abstract powerset conjugation,
with no assumption about preservation of the greatest element. -/
theorem folkmanNativeRingAtomEquiv_map
    {α β : Type*}
    [BooleanRing α] [Fintype α]
    [BooleanRing β] [Fintype β]
    (f : α →ₙ+* β)
    (s : Finset (PrebananaAbstractAtoms (AsBoolAlg α))) :
    (folkmanNativeRingAtomEquiv β)
        (f ((folkmanNativeRingAtomEquiv α).symm s)) =
      prebananaAbstractPowersetMap
        (fun x : AsBoolAlg α => toBoolAlg (f (ofBoolAlg x))) s := by
  classical
  rfl

end SuccessorTree.NonPrecompact
