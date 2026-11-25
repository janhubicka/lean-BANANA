import Mathlib
import BANANA.NonPrecompact.FiniteOwnerSumIdentities

/-!
# Finite sums regrouped by total and partial atom owners

A total owner map assigns every source atom to one target label.
A partial owner map uses `Option`: `none` denotes an unused atom.
The two sum identities work over any commutative additive monoid.

The unital Boolean-algebra embeddings of pre-BANANA use total owners;
the non-unital Boolean-ring embeddings of Folkman–BANANA use partial
owners. The distinction is retained rather than hidden behind a
false equivalence of the embedding notions.
-/
