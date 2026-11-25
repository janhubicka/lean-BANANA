import BANANA.NonPrecompact.PrebananaFiveAryChildMarking
import Mathlib
import BANANA.NonPrecompact.PrebananaFiveAryWordBasics

/-!
# Marks on actual finite words of the five-ary pre-BANANA tower

An atom at level n is an n-letter word over Fin 5. Its mark is
defined by starting with zero at the empty word, and applying the
five-child rule to the final letter at every extension.

This module verifies the actual word-level marking rule. The
finite Boolean stages and marking-preserving connecting embeddings
are constructed in the adjacent five-ary modules. The countable
limit and its finite-extension property remain open.
-/
