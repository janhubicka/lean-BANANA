import BANANA.NonPrecompact.QuadraticResidueStandard
import BANANA.NonPrecompact.SymplecticSlice
import BANANA.NonPrecompact.SymplecticAmalgam

/-!
# Transitive axiom audit for symplectic circulation proofs

The first target is exactly the standard-coordinate quadratic
residue lemma appearing in the circulation manuscript. The other
targets are the codimension-two nondegenerate affine slice and
finite alternating block-amalgam ingredients. They do not, by
themselves, assert the full symplectic Ramsey-degree classification.
-/

#print axioms SuccessorTree.NonPrecompact.quadraticAffineWeight_residueFibres_odd
#print axioms SuccessorTree.NonPrecompact.exists_nondegenerate_codimTwo_slice
#print axioms SuccessorTree.NonPrecompact.symplecticBlockAmalgam_left
#print axioms SuccessorTree.NonPrecompact.symplecticBlockAmalgam_right
#print axioms SuccessorTree.NonPrecompact.symplecticBlockAmalgam_diag_zero
#print axioms SuccessorTree.NonPrecompact.symplecticBlockAmalgam_symmetric
