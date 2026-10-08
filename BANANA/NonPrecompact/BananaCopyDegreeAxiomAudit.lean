import BANANA.NonPrecompact.BananaCopyDegree

/-!
# Axiom audit for the unlabelled-copy degree theorem

Build this file explicitly with Lean/Lake once the toolchain is available.
The output must contain only standard Lean foundational axioms; in
particular `sorryAx` must not occur. The declaration below cannot be
treated as verified merely because it appears in source control.

The root `BANANA.lean` deliberately does not import this file until
a local kernel build of all new modules succeeds.
-/

#print axioms SuccessorTree.NonPrecompact.BananaMatrixEmbedding.exists_linePair_preimage
#print axioms SuccessorTree.NonPrecompact.BananaMatrixEmbedding.linePairPalette_copyRanges
#print axioms SuccessorTree.NonPrecompact.BananaCopyRanges.card_linePairPalette_le_source
#print axioms SuccessorTree.NonPrecompact.card_biUnion_palette_le
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.copyRamseyDegree_infinite_of_positive
