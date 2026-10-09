import BANANA.NonPrecompact.BananaStrongBlockAmalgam

/-!
# Transitive axiom audit for strong split-coordinate BANANA amalgamation

A successful ordinary `BANANA` build is not enough: this file is
deliberately outside the root imports until checked. On the verification
branch, build it explicitly and inspect the output of each command.

Only propext, Quot.sound and Classical.choice are permitted.
-/

#print axioms SuccessorTree.NonPrecompact.indexedBananaPairing_fin_eq_eval
#print axioms SuccessorTree.NonPrecompact.indexedBananaPairing_amalgam_left
#print axioms SuccessorTree.NonPrecompact.indexedBananaPairing_amalgam_right
#print axioms SuccessorTree.NonPrecompact.sumAmalgam_common_agrees
#print axioms SuccessorTree.NonPrecompact.BananaSplitDiagram.left_pairing
#print axioms SuccessorTree.NonPrecompact.BananaSplitDiagram.right_pairing
#print axioms SuccessorTree.NonPrecompact.BananaSplitDiagram.strong_left
#print axioms SuccessorTree.NonPrecompact.BananaSplitDiagram.strong_right
