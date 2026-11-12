import BANANA.NonPrecompact.FolkmanFinitePairedBridgePreorder
import Mathlib.Order.Ideal

/-!
# Cofinal finite paired Folkman bridges from four one-point extensions

This is the two-sorted non-unital adaptation of the already
formalised pre-BANANA cofinal-bridge construction.

The exact finite extension property is packaged as four claims:
a new element can be placed in the source/target copy of either
ring sort while simultaneously extending all four old embeddings
of the bridge. We do NOT assume those one-point extension
properties follow from finite amalgamation without constructing
the countable Folkman limit.

Given those four properties and countability of both ambient sorts,
Mathlib's generic Order.sequenceOfCofinals constructs a monotone
sequence of finite paired bridges, starting at any specified bridge,
whose source and target images cover both sorts.

No unit is named in the embedding language.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- The four one-point extension properties required for a concrete
two-sided back-and-forth construction in the original language. -/
structure FolkmanFinitePairedBridgeOnePointExtension
    (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) : Prop where
  sourceLeft : ∀ (P : FolkmanFinitePairedBridge L R β) (x : L),
    ∃ Q : FolkmanFinitePairedBridge L R β,
      P ≤ Q ∧ ∃ a, Q.source.left a = x
  targetLeft : ∀ (P : FolkmanFinitePairedBridge L R β) (x : L),
    ∃ Q : FolkmanFinitePairedBridge L R β,
      P ≤ Q ∧ ∃ a, Q.targetLeft a = x
  sourceRight : ∀ (P : FolkmanFinitePairedBridge L R β) (y : R),
    ∃ Q : FolkmanFinitePairedBridge L R β,
      P ≤ Q ∧ ∃ a, Q.source.right a = y
  targetRight : ∀ (P : FolkmanFinitePairedBridge L R β) (y : R),
    ∃ Q : FolkmanFinitePairedBridge L R β,
      P ≤ Q ∧ ∃ a, Q.targetRight a = y

namespace FolkmanFinitePairedBridgeOnePointExtension

variable {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
variable {β : L → R → F2}

/-- Bridges whose source left copy contains the given element are cofinal. -/
noncomputable def sourceLeftCofinal
    (H : FolkmanFinitePairedBridgeOnePointExtension L R β)
    (x : L) :
    Order.Cofinal (FolkmanFinitePairedBridge L R β) where
  carrier := {P | ∃ a, P.source.left a = x}
  isCofinal := by
    intro P
    obtain ⟨Q, hPQ, hx⟩ := H.sourceLeft P x
    exact ⟨Q, hx, hPQ⟩

/-- Bridges whose target left copy contains the given element are cofinal. -/
noncomputable def targetLeftCofinal
    (H : FolkmanFinitePairedBridgeOnePointExtension L R β)
    (x : L) :
    Order.Cofinal (FolkmanFinitePairedBridge L R β) where
  carrier := {P | ∃ a, P.targetLeft a = x}
  isCofinal := by
    intro P
    obtain ⟨Q, hPQ, hx⟩ := H.targetLeft P x
    exact ⟨Q, hx, hPQ⟩

/-- The source right copy can be extended to cover any ambient element. -/
noncomputable def sourceRightCofinal
    (H : FolkmanFinitePairedBridgeOnePointExtension L R β)
    (y : R) :
    Order.Cofinal (FolkmanFinitePairedBridge L R β) where
  carrier := {P | ∃ a, P.source.right a = y}
  isCofinal := by
    intro P
    obtain ⟨Q, hPQ, hy⟩ := H.sourceRight P y
    exact ⟨Q, hy, hPQ⟩

/-- The target right copy can be extended to cover any ambient element. -/
noncomputable def targetRightCofinal
    (H : FolkmanFinitePairedBridgeOnePointExtension L R β)
    (y : R) :
    Order.Cofinal (FolkmanFinitePairedBridge L R β) where
  carrier := {P | ∃ a, P.targetRight a = y}
  isCofinal := by
    intro P
    obtain ⟨Q, hPQ, hy⟩ := H.targetRight P y
    exact ⟨Q, hy, hPQ⟩

/-- Fair dovetailing of all four requirements gives an exhaustive
monotone chain of actual paired finite Folkman bridges.

This is a construction from explicit *one-point* extension
hypotheses, not an unconditional construction of the Fraisse limit. -/
theorem exists_exhaustive_chain
    [Countable L] [Countable R]
    (H : FolkmanFinitePairedBridgeOnePointExtension L R β)
    (initial : FolkmanFinitePairedBridge L R β) :
    ∃ chain : ℕ → FolkmanFinitePairedBridge L R β,
      chain 0 = initial ∧
      Monotone chain ∧
      (∀ x : L, ∃ n : ℕ, ∃ a, (chain n).source.left a = x) ∧
      (∀ x : L, ∃ n : ℕ, ∃ a, (chain n).targetLeft a = x) ∧
      (∀ y : R, ∃ n : ℕ, ∃ b, (chain n).source.right b = y) ∧
      (∀ y : R, ∃ n : ℕ, ∃ b, (chain n).targetRight b = y) := by
  classical
  letI : Encodable (Sum (Sum L R) (Sum L R)) :=
    Encodable.ofCountable _
  let D : Sum (Sum L R) (Sum L R) →
      Order.Cofinal (FolkmanFinitePairedBridge L R β) :=
    Sum.elim
      (Sum.elim (H.sourceLeftCofinal) (H.sourceRightCofinal))
      (Sum.elim (H.targetLeftCofinal) (H.targetRightCofinal))
  let chain : ℕ → FolkmanFinitePairedBridge L R β :=
    Order.sequenceOfCofinals initial D
  refine ⟨chain, rfl, Order.sequenceOfCofinals.monotone initial D,
    ?_, ?_, ?_, ?_⟩
  · intro x
    have h := Order.sequenceOfCofinals.encode_mem initial D
      (Sum.inl (Sum.inl x) : Sum (Sum L R) (Sum L R))
    exact ⟨Encodable.encode (Sum.inl (Sum.inl x) :
      Sum (Sum L R) (Sum L R)) + 1, h⟩
  · intro x
    have h := Order.sequenceOfCofinals.encode_mem initial D
      (Sum.inr (Sum.inl x) : Sum (Sum L R) (Sum L R))
    exact ⟨Encodable.encode (Sum.inr (Sum.inl x) :
      Sum (Sum L R) (Sum L R)) + 1, h⟩
  · intro y
    have h := Order.sequenceOfCofinals.encode_mem initial D
      (Sum.inl (Sum.inr y) : Sum (Sum L R) (Sum L R))
    exact ⟨Encodable.encode (Sum.inl (Sum.inr y) :
      Sum (Sum L R) (Sum L R)) + 1, h⟩
  · intro y
    have h := Order.sequenceOfCofinals.encode_mem initial D
      (Sum.inr (Sum.inr y) : Sum (Sum L R) (Sum L R))
    exact ⟨Encodable.encode (Sum.inr (Sum.inr y) :
      Sum (Sum L R) (Sum L R)) + 1, h⟩

end FolkmanFinitePairedBridgeOnePointExtension
end SuccessorTree.NonPrecompact
