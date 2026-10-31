import BANANA.NonPrecompact.CoherentEppaRepresentativeTransport
import BANANA.NonPrecompact.CoherentEppaPackage

/-!
# Track D: transitive axiom audits for coherent EPPA constituents

The checks below must be run with the pinned Lean toolchain on the exact
head SHA. No result is asserted without a successful local kernel run.
-/

#print axioms SuccessorTree.NonPrecompact.conjugatedTransport_one
#print axioms SuccessorTree.NonPrecompact.conjugatedTransport_mul
#print axioms SuccessorTree.NonPrecompact.conjugatedTransport_inv
#print axioms SuccessorTree.NonPrecompact.conjugatedTransport_representative_smul
#print axioms SuccessorTree.NonPrecompact.conjugatedTransport_extends_two_sorts
#print axioms SuccessorTree.NonPrecompact.BananaMatrixStructure.exists_alignedCoherentAmbientAction
