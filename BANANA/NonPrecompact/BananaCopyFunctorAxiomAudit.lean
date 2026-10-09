import BANANA.NonPrecompact.BananaCopyFunctor

/-!
# Transitive axiom audit for functorial unlabelled copies

Run this file with the pinned Lean toolchain, locally. The presence
of a declaration or a #print axioms command in the repository does not
show that the proof has passed kernel checking.

Only propext, Quot.sound, and Classical.choice are acceptable transitive
axiom dependencies. In particular sorryAx must not occur.
-/

#print axioms SuccessorTree.NonPrecompact.BananaCopyRanges.map_comp
#print axioms SuccessorTree.NonPrecompact.BananaCopyRanges.map_identity
#print axioms SuccessorTree.NonPrecompact.BananaCopyRanges.map_injective
#print axioms SuccessorTree.NonPrecompact.BananaLinePairCopy.exists_preimage_of_in_mapped_copy
#print axioms SuccessorTree.NonPrecompact.BananaCopyRanges.linePairPalette_map
