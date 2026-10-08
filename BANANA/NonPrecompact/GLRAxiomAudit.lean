import BANANA.NonPrecompact.LinearBinaryRepresentability

/-!
# Axiom audit for the binary subspace Ramsey derivation

The four commands below print the transitive logical axioms of the
unconditional finite-dimensional representation theorem, binary
Graham--Leeb--Rothschild property, and both one-sided BANANA copy-Ramsey
statements.  This module is imported by the root package during the
formalisation audit, so the results appear in its build log.

The expected foundational axioms are Lean's standard logical axioms,
in particular `propext`, `Quot.sound` and `Classical.choice`.
Any theorem-specific or `sorryAx` dependency must be investigated.
-/

#print axioms SuccessorTree.NonPrecompact.BinaryWord.everyBinarySubspaceRepresentable
#print axioms SuccessorTree.NonPrecompact.BinaryWord.binarySubspaceRamsey_via_successors
#print axioms SuccessorTree.NonPrecompact.BinaryWord.leftOneSidedCopyRamseyOne_via_successors
#print axioms SuccessorTree.NonPrecompact.BinaryWord.rightOneSidedCopyRamseyOne_via_successors
