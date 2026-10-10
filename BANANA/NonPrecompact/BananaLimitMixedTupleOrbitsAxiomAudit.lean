import BANANA.NonPrecompact.BananaLimitMixedTupleOrbits

/-!
# Axiom audit for mixed-sort oligomorphicity

Each tuple position belongs to one of the two sorts. This audit
checks that the finite sort-pattern/signature invariant yields a
genuine global pairing-preserving automorphism and finitely many
representatives for every tuple length.

The general Ryll–Nardzewski omega-categoricity theorem is not
formalised here.
-/

#print axioms SuccessorTree.NonPrecompact.bananaLimitTaggedSignature_finite
#print axioms SuccessorTree.NonPrecompact.bananaLimitTaggedOrbitRelated_of_signature_eq
#print axioms SuccessorTree.NonPrecompact.bananaLimit_exists_finite_tagged_tuple_orbit_representatives
