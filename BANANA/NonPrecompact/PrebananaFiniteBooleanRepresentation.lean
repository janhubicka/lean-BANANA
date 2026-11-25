import BANANA.NonPrecompact.PrebananaPowersetStrongAmalgam
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Atoms
import BANANA.NonPrecompact.PrebananaFiniteBooleanCoordinates

/-!
# Finite Boolean algebras as powersets of their atoms

This is the representation interface between the abstract Boolean
algebras used in the Boolean–BANANA manuscript and the atom-coordinate
Lean implementation.

Mathlib supplies both the canonical representation theorem for
complete atomic Boolean algebras and the finite completeness
construction. This module combines them without additional axioms.

The induced marking from a Boolean-algebra parity map and the
translation of arbitrary unital embeddings remain separate steps.
-/
