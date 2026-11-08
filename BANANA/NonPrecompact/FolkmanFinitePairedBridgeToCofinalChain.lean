import BANANA.NonPrecompact.FolkmanFinitePairedBridgeCofinal
import BANANA.NonPrecompact.FolkmanCofinalBridgeChain

/-!
# From a monotone sequence of finite paired bridges to a coherent chain

All coherence and pairwise common-refinement hypotheses of
FolkmanCofinalBridgeChain are derived from ONE monotonicity assumption
on genuine finite bridge extensions.

For indices n,m pass to k=max(n,m), and choose the two finite
bridge maps supplied by the extension preorder. Their four
commuting squares identify original ambient elements on both
source and target copies. Injectivity of either copy proves
representative independence in both directions.

This is a reusable algebraic step, independent of any countable
Fraisse-limit existence or one-point extension assertion.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- A monotone, exhaustive sequence of finite paired bridges
has all the coherence data required to construct a global
two-sort non-unital pairing automorphism. -/
noncomputable def folkmanCofinalBridgeChain_of_monotone
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (chain : ℕ → FolkmanFinitePairedBridge L R β)
    (hmono : Monotone chain)
    (hSL : ∀ x : L, ∃ n, ∃ a, (chain n).source.left a = x)
    (hTL : ∀ x : L, ∃ n, ∃ a, (chain n).targetLeft a = x)
    (hSR : ∀ y : R, ∃ n, ∃ b, (chain n).source.right b = y)
    (hTR : ∀ y : R, ∃ n, ∃ b, (chain n).targetRight b = y) :
    FolkmanCofinalBridgeChain L R β where
  code := fun n => (chain n).source.atom
  sourceLeft := fun n => (chain n).source.left
  targetLeft := fun n => (chain n).targetLeft
  sourceRight := fun n => (chain n).source.right
  targetRight := fun n => (chain n).targetRight
  sourceLeft_injective := fun n => (chain n).source.left_injective
  targetLeft_injective := fun n => (chain n).targetLeft_injective
  sourceRight_injective := fun n => (chain n).source.right_injective
  targetRight_injective := fun n => (chain n).targetRight_injective
  source_stage_pairing := by
    intro n a b
    simpa only [toBoolRing_ofBoolRing] using
      ((chain n).source.preserves_pairing (ofBoolRing a) (ofBoolRing b))
  target_stage_pairing := by
    intro n a b
    simpa only [toBoolRing_ofBoolRing] using
      ((chain n).target_pairing (ofBoolRing a) (ofBoolRing b))
  left_forward_coherent := by
    intro n m a b h
    let k := max n m
    let f : FolkmanFinitePairedBridgeMap (chain n) (chain k) :=
      Classical.choice (hmono (le_max_left n m))
    let g : FolkmanFinitePairedBridgeMap (chain m) (chain k) :=
      Classical.choice (hmono (le_max_right n m))
    have hsame : f.left a = g.left b := by
      apply (chain k).source.left_injective
      calc
        (chain k).source.left (f.left a) =
            (chain n).source.left a := f.source_left_comm a
        _ = (chain m).source.left b := h
        _ = (chain k).source.left (g.left b) :=
          (g.source_left_comm b).symm
    calc
      (chain n).targetLeft a =
          (chain k).targetLeft (f.left a) :=
        (f.target_left_comm a).symm
      _ = (chain k).targetLeft (g.left b) :=
        congrArg (chain k).targetLeft hsame
      _ = (chain m).targetLeft b :=
        g.target_left_comm b
  left_backward_coherent := by
    intro n m a b h
    let k := max n m
    let f : FolkmanFinitePairedBridgeMap (chain n) (chain k) :=
      Classical.choice (hmono (le_max_left n m))
    let g : FolkmanFinitePairedBridgeMap (chain m) (chain k) :=
      Classical.choice (hmono (le_max_right n m))
    have hsame : f.left a = g.left b := by
      apply (chain k).targetLeft_injective
      calc
        (chain k).targetLeft (f.left a) =
            (chain n).targetLeft a := f.target_left_comm a
        _ = (chain m).targetLeft b := h
        _ = (chain k).targetLeft (g.left b) :=
          (g.target_left_comm b).symm
    calc
      (chain n).source.left a =
          (chain k).source.left (f.left a) :=
        (f.source_left_comm a).symm
      _ = (chain k).source.left (g.left b) :=
        congrArg (chain k).source.left hsame
      _ = (chain m).source.left b :=
        g.source_left_comm b
  right_forward_coherent := by
    intro n m a b h
    let k := max n m
    let f : FolkmanFinitePairedBridgeMap (chain n) (chain k) :=
      Classical.choice (hmono (le_max_left n m))
    let g : FolkmanFinitePairedBridgeMap (chain m) (chain k) :=
      Classical.choice (hmono (le_max_right n m))
    have hsame : f.right a = g.right b := by
      apply (chain k).source.right_injective
      calc
        (chain k).source.right (f.right a) =
            (chain n).source.right a := f.source_right_comm a
        _ = (chain m).source.right b := h
        _ = (chain k).source.right (g.right b) :=
          (g.source_right_comm b).symm
    calc
      (chain n).targetRight a =
          (chain k).targetRight (f.right a) :=
        (f.target_right_comm a).symm
      _ = (chain k).targetRight (g.right b) :=
        congrArg (chain k).targetRight hsame
      _ = (chain m).targetRight b :=
        g.target_right_comm b
  right_backward_coherent := by
    intro n m a b h
    let k := max n m
    let f : FolkmanFinitePairedBridgeMap (chain n) (chain k) :=
      Classical.choice (hmono (le_max_left n m))
    let g : FolkmanFinitePairedBridgeMap (chain m) (chain k) :=
      Classical.choice (hmono (le_max_right n m))
    have hsame : f.right a = g.right b := by
      apply (chain k).targetRight_injective
      calc
        (chain k).targetRight (f.right a) =
            (chain n).targetRight a := f.target_right_comm a
        _ = (chain m).targetRight b := h
        _ = (chain k).targetRight (g.right b) :=
          (g.target_right_comm b).symm
    calc
      (chain n).source.right a =
          (chain k).source.right (f.right a) :=
        (f.source_right_comm a).symm
      _ = (chain k).source.right (g.right b) :=
        congrArg (chain k).source.right hsame
      _ = (chain m).source.right b :=
        g.source_right_comm b
  commonLeft := by
    intro n m a b
    let k := max n m
    let f : FolkmanFinitePairedBridgeMap (chain n) (chain k) :=
      Classical.choice (hmono (le_max_left n m))
    let g : FolkmanFinitePairedBridgeMap (chain m) (chain k) :=
      Classical.choice (hmono (le_max_right n m))
    exact ⟨k, f.left a, g.left b,
      f.source_left_comm a, f.target_left_comm a,
      g.source_left_comm b, g.target_left_comm b⟩
  commonRight := by
    intro n m a b
    let k := max n m
    let f : FolkmanFinitePairedBridgeMap (chain n) (chain k) :=
      Classical.choice (hmono (le_max_left n m))
    let g : FolkmanFinitePairedBridgeMap (chain m) (chain k) :=
      Classical.choice (hmono (le_max_right n m))
    exact ⟨k, f.right a, g.right b,
      f.source_right_comm a, f.target_right_comm a,
      g.source_right_comm b, g.target_right_comm b⟩
  commonPair := by
    intro n m a b
    let k := max n m
    let f : FolkmanFinitePairedBridgeMap (chain n) (chain k) :=
      Classical.choice (hmono (le_max_left n m))
    let g : FolkmanFinitePairedBridgeMap (chain m) (chain k) :=
      Classical.choice (hmono (le_max_right n m))
    exact ⟨k, f.left a, g.right b,
      f.source_left_comm a, f.target_left_comm a,
      g.source_right_comm b, g.target_right_comm b⟩
  sourceLeft_exhaustive := hSL
  targetLeft_exhaustive := hTL
  sourceRight_exhaustive := hSR
  targetRight_exhaustive := hTR

/-- Given countability and the four one-point extension properties,
any initial finite bridge extends to a cofinal chain satisfying
the exact hypotheses of the previously drafted global automorphism. -/
noncomputable def folkmanCofinalBridgeChain_of_onePointExtensions
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (H : FolkmanFinitePairedBridgeOnePointExtension L R β)
    (initial : FolkmanFinitePairedBridge L R β) :
    FolkmanCofinalBridgeChain L R β := by
  classical
  obtain ⟨chain, hzero, hmono, hSL, hTL, hSR, hTR⟩ :=
    H.exists_exhaustive_chain initial
  exact folkmanCofinalBridgeChain_of_monotone
    chain hmono hSL hTL hSR hTR

end SuccessorTree.NonPrecompact
