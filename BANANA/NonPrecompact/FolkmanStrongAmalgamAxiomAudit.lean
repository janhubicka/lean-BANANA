import BANANA.NonPrecompact.FolkmanAtomAmalgam
import BANANA.NonPrecompact.FolkmanBilinearExtension

/-!
# Transitive axiom audit of the Folkman--BANANA finite strong-amalgam layers

The finite Boolean-ring atom-grid-with-private-points construction
has an exact strong intersection property. For the two-sorted
pairing, a zero-extended block matrix restricts to both input
systems, and the resulting linear images intersect exactly over
the common base.

These are the two explicit algebraic interfaces used in the
circulation proof. This audit does not itself package a Fraïssé
class of non-unital two-sorted Boolean rings, or formalise the
final passage to its countable Fraïssé limit.
-/

#print axioms SuccessorTree.NonPrecompact.exists_common_subset_of_folkmanAtomAmalgam
#print axioms SuccessorTree.NonPrecompact.folkmanBilinearAmalgam_left
#print axioms SuccessorTree.NonPrecompact.folkmanBilinearAmalgam_right
#print axioms SuccessorTree.NonPrecompact.folkmanAmalgamLinear_eq_iff_common
#print axioms SuccessorTree.NonPrecompact.matrixExtendZero_old
