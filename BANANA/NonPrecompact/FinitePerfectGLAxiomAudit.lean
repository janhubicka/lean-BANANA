import BANANA.NonPrecompact.FinitePerfectGL

/-!
# Finite perfect-pair GL stage: transitive axiom audit

This file verifies the exact finite algebraic assertions used in the
amenability proof. It does not assert density of their direct limit
in the infinite automorphism group or topological amenability.

The checks must be executed by Lean's kernel. Only the standard
foundation axioms `propext`, `Classical.choice`, and `Quot.sound`
are allowed in their transitive dependencies.
-/

#print axioms SuccessorTree.NonPrecompact.finitePerfectGLFinite
#print axioms SuccessorTree.NonPrecompact.FinitePerfectGL.pairing_preserved
#print axioms SuccessorTree.NonPrecompact.finitePerfectGLBlockLift_first
#print axioms SuccessorTree.NonPrecompact.finitePerfectGLBlockLift_second
#print axioms SuccessorTree.NonPrecompact.finitePerfectGLBlockLift_refl
#print axioms SuccessorTree.NonPrecompact.finitePerfectGLBlockLift_trans
#print axioms SuccessorTree.NonPrecompact.finitePerfectGLBlockLift_injective
#print axioms SuccessorTree.NonPrecompact.finitePerfectGLBlockLift_automorphism_right_first
#print axioms SuccessorTree.NonPrecompact.finitePerfectGLBlockLift_automorphism_right_complement
