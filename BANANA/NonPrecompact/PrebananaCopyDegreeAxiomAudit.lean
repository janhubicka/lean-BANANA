import BANANA.NonPrecompact.PrebananaCopyDegree
import BANANA.NonPrecompact.ColouringWrappers

/-!
# Transitive axiom audit of pre-BANANA persistent copy colouring

The circulation theorem constructs a colouring of unlabelled copies
of the two-marked-atom source such that every all-marked power-of-two
target contains all its prescribed colours, ruling out every finite
copy Ramsey-degree bound. These axioms must be standard Lean logical
axioms only, with no sorryAx or extra persistent-colouring hypothesis.
-/

#print axioms SuccessorTree.NonPrecompact.prebanana_odd_residue_copy_witness
#print axioms SuccessorTree.NonPrecompact.exists_prebananaPersistentColouring
#print axioms SuccessorTree.NonPrecompact.prebananaTwoMarkedCopyRamseyDegree_infinite
