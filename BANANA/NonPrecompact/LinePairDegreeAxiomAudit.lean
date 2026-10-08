import BANANA.NonPrecompact.BananaEmbeddingDegree

/-!
# Audit of the two-sided BANANA degree extension

When this module is built by Lean, the commands below print the transitive
logical axioms of the new structural-embedding obstruction. The expected
axioms are only Lean's ordinary foundations (`propext`, `Quot.sound`,
`Classical.choice`). A `sorryAx` or theorem-specific axiom must be
investigated before the results are marked verified in the manuscript.

This file is a declaration-level audit; the presence of these commands
alone is **not** a successful kernel build.
-/

#print axioms SuccessorTree.NonPrecompact.linePairEmbeddingRamseyDegree_infinite
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.exists_linePairExtension_in_perfectBlock
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.exists_extend_linePairCopy
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.embeddingRamseyDegree_infinite_of_positive
