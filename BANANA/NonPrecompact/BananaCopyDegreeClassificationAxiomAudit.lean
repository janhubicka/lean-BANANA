import BANANA.NonPrecompact.BananaOneSidedCopyDegree

/-!
# Axiom audit: complete copy Ramsey-degree classification for BANANA

The terminal theorem treats actual unlabelled copy-colourings of
finite BANANA pairing structures: one-sided sources have degree one,
while sources involving both sorts have infinite finite degree.
The following declarations must depend only on Lean's standard
foundational axioms, and never on a staged Ramsey axiom or sorryAx.
-/

#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.copyRamseyDegreeLE_one_leftOnly
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.copyRamseyDegreeLE_one_rightOnly
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.not_copyRamseyDegreeLE_zero
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.copyRamseyDegree_classification
