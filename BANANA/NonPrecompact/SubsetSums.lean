import Mathlib
import BANANA.NonPrecompact.IndexedSubsetSums

/-!
# Subset-sum lower bounds for the non-precompact colourings

This file formalises the common combinatorial core of the pre-BANANA and
Folkman--BANANA persistent colourings.

The paper uses the following elementary fact. If `q` is a power of two,
then the subset sums of any `q - 1` odd integers cover every residue modulo
`q`. We prove a slightly more general statement: over `ZMod q`, `q - 1`
weights that are units have all residues as indexed subset sums.

The proof follows the manuscript. Starting from `{0}`, adjoining a unit
strictly enlarges the set of attainable sums unless it is already all of
`ZMod q`. Translation by a unit generates the additive cyclic group.
-/
