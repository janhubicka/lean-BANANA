import BANANA.NonPrecompact.BananaOneSidedCopyDegree

/-!
# Axiom audit for the common unlabelled-copy Ramsey-degree classification

This is deliberately not imported by root BANANA.lean until a local Lean
kernel build has succeeded. The expected axiom set is limited to the
ordinary Lean logical foundations (propext, Classical.choice, Quot.sound).

A #print axioms command is an *instruction to the compiler*, not proof
that the declarations compile; its output must be inspected after the
local build. Neither GitHub Actions nor remote runners should be used.
-/

#print axioms SuccessorTree.NonPrecompact.BananaCopyRanges.leftFixedSubspace_injective
#print axioms SuccessorTree.NonPrecompact.BananaCopyRanges.rightFixedSubspace_injective
#print axioms SuccessorTree.NonPrecompact.BananaCopyRanges.leftFixedSubspace_map
#print axioms SuccessorTree.NonPrecompact.BananaCopyRanges.rightFixedSubspace_map
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.copyRamseyDegreeLE_one_leftOnly
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.copyRamseyDegreeLE_one_rightOnly
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.not_copyRamseyDegreeLE_zero
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.copyRamseyDegree_classification
