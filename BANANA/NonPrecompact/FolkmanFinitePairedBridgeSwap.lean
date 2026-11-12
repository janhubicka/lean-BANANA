import BANANA.NonPrecompact.FolkmanFinitePairedBridgeCofinal

/-!
# Back-and-forth symmetry of paired finite Folkman bridges

A finite paired bridge is symmetric in its two embeddings: swapping
source and target preserves the same finite atom code and its *full*
F₂-valued pairing. An extension commutes with four ambient maps,
so the same finite ring maps also extend the swapped bridge.

Consequently it suffices to prove two one-point **forth** extension
properties (one for each original ring sort). The target-side
requirements follow by swapping, without repeating strong AP or
adding a multiplicative unit. This does not claim that the two
forth-extension properties already hold for a countable limit.
-/

namespace SuccessorTree.NonPrecompact

/-- Exchange the two actual copies of one finite Folkman object.
Both reconstruct exactly the same original cross-sort pairing. -/
def FolkmanFinitePairedBridge.swap
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (P : FolkmanFinitePairedBridge L R β) :
    FolkmanFinitePairedBridge L R β where
  source := {
    atom := P.source.atom
    left := P.targetLeft
    right := P.targetRight
    left_injective := P.targetLeft_injective
    right_injective := P.targetRight_injective
    preserves_pairing := P.target_pairing
  }
  targetLeft := P.source.left
  targetRight := P.source.right
  targetLeft_injective := P.source.left_injective
  targetRight_injective := P.source.right_injective
  target_pairing := P.source.preserves_pairing

/-- Swapping twice recovers the original two embeddings. -/
theorem FolkmanFinitePairedBridge.swap_swap
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (P : FolkmanFinitePairedBridge L R β) :
    P.swap.swap = P := by
  cases P
  rfl

/-- The same finite code embedding extends the swapped bridge,
with source and target commutative squares exchanged. -/
def FolkmanFinitePairedBridgeMap.swap
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    {P Q : FolkmanFinitePairedBridge L R β}
    (f : FolkmanFinitePairedBridgeMap P Q) :
    FolkmanFinitePairedBridgeMap P.swap Q.swap where
  left := f.left
  right := f.right
  left_injective := f.left_injective
  right_injective := f.right_injective
  source_left_comm := f.target_left_comm
  target_left_comm := f.source_left_comm
  source_right_comm := f.target_right_comm
  target_right_comm := f.source_right_comm

/-- Hence bridge extension is preserved by exchanging source and target. -/
theorem folkmanFinitePairedBridge_swap_monotone
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    {P Q : FolkmanFinitePairedBridge L R β}
    (h : P ≤ Q) : P.swap ≤ Q.swap := by
  obtain ⟨f⟩ := h
  exact ⟨f.swap⟩

/-- Only the two source-side one-point extension properties need
be supplied from the actual countable Folkman limit. -/
structure FolkmanFinitePairedBridgeForthExtension
    (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) : Prop where
  sourceLeft : ∀ (P : FolkmanFinitePairedBridge L R β) (x : L),
    ∃ Q : FolkmanFinitePairedBridge L R β,
      P ≤ Q ∧ ∃ a, Q.source.left a = x
  sourceRight : ∀ (P : FolkmanFinitePairedBridge L R β) (y : R),
    ∃ Q : FolkmanFinitePairedBridge L R β,
      P ≤ Q ∧ ∃ b, Q.source.right b = y

/-- Forth extension of the swapped finite bridge supplies the
target-left back extension of the original finite bridge. -/
theorem FolkmanFinitePairedBridgeForthExtension.targetLeft
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (H : FolkmanFinitePairedBridgeForthExtension L R β)
    (P : FolkmanFinitePairedBridge L R β) (x : L) :
    ∃ Q : FolkmanFinitePairedBridge L R β,
      P ≤ Q ∧ ∃ a, Q.targetLeft a = x := by
  obtain ⟨Q, hPQ, ⟨a, ha⟩⟩ := H.sourceLeft P.swap x
  refine ⟨Q.swap, ?_, ?_⟩
  · have hswap : P.swap ≤ Q := hPQ
    have h := folkmanFinitePairedBridge_swap_monotone hswap
    simpa only [FolkmanFinitePairedBridge.swap_swap] using h
  · exact ⟨a, ha⟩

/-- Likewise for target-right: no fourth independent extension
theorem is required. -/
theorem FolkmanFinitePairedBridgeForthExtension.targetRight
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (H : FolkmanFinitePairedBridgeForthExtension L R β)
    (P : FolkmanFinitePairedBridge L R β) (y : R) :
    ∃ Q : FolkmanFinitePairedBridge L R β,
      P ≤ Q ∧ ∃ a, Q.targetRight a = y := by
  obtain ⟨Q, hPQ, ⟨a, ha⟩⟩ := H.sourceRight P.swap y
  refine ⟨Q.swap, ?_, ?_⟩
  · have hswap : P.swap ≤ Q := hPQ
    have h := folkmanFinitePairedBridge_swap_monotone hswap
    simpa only [FolkmanFinitePairedBridge.swap_swap] using h
  · exact ⟨a, ha⟩

/-- Two source-side extension properties imply all four properties
needed by the existing cofinal bridge-chain construction. -/
def FolkmanFinitePairedBridgeForthExtension.toOnePointExtension
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (H : FolkmanFinitePairedBridgeForthExtension L R β) :
    FolkmanFinitePairedBridgeOnePointExtension L R β where
  sourceLeft := H.sourceLeft
  targetLeft := H.targetLeft
  sourceRight := H.sourceRight
  targetRight := H.targetRight

end SuccessorTree.NonPrecompact
