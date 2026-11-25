import BANANA.NonPrecompact.PrebananaFiniteBooleanCoordinates

/-!
# Conjugating arbitrary finite Boolean embeddings to atom powersets

Every finite Boolean algebra is canonically an atom powerset, as
formalised in `PrebananaFiniteBooleanRepresentation`. A map
preserving bottom, top, joins, and meets becomes a map of finite
atom subsets preserving empty, full, union, and intersection.
Injectivity is also preserved. No marking assumptions are
needed for this Boolean-algebraic step.

This is the abstract side of the converse atom-partition theorem.
-/
