import BANANA.NonPrecompact.SubsetSums
import BANANA.NonPrecompact.ColouringWrappers
import BANANA.NonPrecompact.PrebananaResidueBlocks

/-!
# Nonempty odd subset sums for pre-BANANA residue realisation

The circulation proof of the pre-BANANA finite-residue realisation lemma
needs a strengthening of the basic subset-sum theorem.  With exactly
`q = 2^k` odd weights, every residue modulo `q` is represented by a
nonempty subset.

For a nonzero target residue, apply the existing `q-1` theorem after
reserving one weight; the empty subset cannot realise a nonzero residue.
For the zero residue, use the reserved weight and choose a subset of the
remaining weights which cancels it.
-/
