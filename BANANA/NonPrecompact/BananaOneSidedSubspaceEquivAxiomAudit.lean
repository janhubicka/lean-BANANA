import BANANA.NonPrecompact.BananaOneSidedSubspaceEquiv

/-!
# Axiom audit: one-sided copies versus subspaces

Build this file locally with the pinned Lean/Lake/Mathlib toolchain.
Its presence in the repository does NOT mean that the new declarations
are kernel-verified. Verify the transitive axiom sets and ensure that
`sorryAx` does not occur before using manuscript validation markers.

The file is intentionally not imported from the root BANANA package
until the targeted Lean check has passed.
-/

#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.exists_leftOnlyCopy_overSubspace
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.exists_rightOnlyCopy_overSubspace
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.leftOnlyCopySubspaceEquiv
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.rightOnlyCopySubspaceEquiv
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.copyRamseyDegree_classification
