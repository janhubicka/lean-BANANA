import BANANA.NonPrecompact.BooleanSpectrum

/-! Kernel axiom audit for the Boolean Stone space and its induced action maps. -/

#print axioms SuccessorTree.NonPrecompact.BooleanSpectrum.clopens
#print axioms SuccessorTree.NonPrecompact.BooleanSpectrum.toSets
#print axioms SuccessorTree.NonPrecompact.BooleanSpectrum.isTopologicalBasis_clopens
#print axioms SuccessorTree.NonPrecompact.BooleanSpectrum.instTotallySeparatedSpace
#print axioms SuccessorTree.NonPrecompact.BooleanSpectrum.instNonempty
#print axioms SuccessorTree.NonPrecompact.BooleanSpectrum.instSecondCountableTopology
#print axioms SuccessorTree.NonPrecompact.BooleanSpectrum.preimage_homeomorph_clopens
#print axioms SuccessorTree.NonPrecompact.BooleanSpectrum.continuous_homeomorph

open SuccessorTree.NonPrecompact.BooleanSpectrum TopologicalSpace

example (B : Type*) [BooleanAlgebra B] [Nontrivial B] [Countable B] :
    Nonempty (Space B) ∧ CompactSpace (Space B) ∧ T2Space (Space B) ∧
      MetrizableSpace (Space B) :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
