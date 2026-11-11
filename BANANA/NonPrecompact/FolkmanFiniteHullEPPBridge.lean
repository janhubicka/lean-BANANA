import BANANA.NonPrecompact.FolkmanFinitePairedBridgeSwap
import BANANA.NonPrecompact.FolkmanForthBridgeHomogeneity

/-!
# From finite ambient hulls and EPP to Folkman forth extensions

The countable Folkman limit still needs to be constructed. The
next step of the *conditional* back-and-forth proof is nevertheless
independent of that construction: a finite stage hull of the source
copy of one paired bridge, together with the ordinary finite
embedding-extension property (EPP), extends the bridge.

We express finite embeddings between atom-coded original-language
objects by injective non-unital ring maps on both sorts preserving
the FULL finite matrix pairing. Neither side's multiplicative unit
is named or required to be preserved.

Given an ambient finite stage containing a source bridge copy,
EPP extends the target copy to that finite stage. This yields one
larger genuine paired bridge. The swap theorem derives the two
back extensions, so there are only TWO hull conditions to prove.

This file does not assert the actual limit exists or that it has
the stated finite hull and EPP properties.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- An embedding of two finite atom codes in the actual non-unital
two-sort pairing language. The matrix condition holds for every
ring element, not merely the distinguished atom generators. -/
structure FolkmanFiniteCodeEmbedding
    (A B : FolkmanAtomStructure) where
  left :
    AsBoolRing (Finset (Fin A.leftCount)) →ₙ+*
      AsBoolRing (Finset (Fin B.leftCount))
  right :
    AsBoolRing (Finset (Fin A.rightCount)) →ₙ+*
      AsBoolRing (Finset (Fin B.rightCount))
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  pairing : ∀ (s : Finset (Fin A.leftCount))
      (t : Finset (Fin A.rightCount)),
    (∑ i ∈ ofBoolRing (left (toBoolRing s)),
       ∑ j ∈ ofBoolRing (right (toBoolRing t)), B.edge i j) =
      ∑ i ∈ s, ∑ j ∈ t, A.edge i j

/-- A faithful finite atom stage containing the original source
copy of a paired bridge. The embedded code map reproduces BOTH
source-ring maps on all code elements, not just a selected tuple. -/
structure FolkmanPairedBridgeSourceHull
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (P : FolkmanFinitePairedBridge L R β) where
  stage : FolkmanFiniteAtomStage L R β
  embedding : FolkmanFiniteCodeEmbedding P.source.atom stage.atom
  left_commutes : ∀ x,
    stage.left (embedding.left x) = P.source.left x
  right_commutes : ∀ y,
    stage.right (embedding.right y) = P.source.right y

/-- The two required finite hull properties in the original
non-unital ambient language, with the whole source bridge copy
retained. Covering only the named tuple would be insufficient. -/
structure FolkmanPairedBridgeSourceHullProperty
    (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) : Prop where
  left : ∀ (P : FolkmanFinitePairedBridge L R β) (x : L),
    ∃ H : FolkmanPairedBridgeSourceHull P,
      ∃ a, H.stage.left a = x
  right : ∀ (P : FolkmanFinitePairedBridge L R β) (y : R),
    ∃ H : FolkmanPairedBridgeSourceHull P,
      ∃ b, H.stage.right b = y

/-- Finite embedding-extension property for all original atom-coded
finite Folkman objects. Extending an embedding of the original
finite source code into the ambient pairing along an injective
finite code map produces a faithful embedding of the larger code.

The equation is demanded on every source ring element, and the
pairing reconstruction on every pair of target elements. -/
structure FolkmanFiniteCodeEPP
    (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) : Prop where
  extend : ∀
    (S : FolkmanFiniteAtomStage L R β)
    (B : FolkmanAtomStructure)
    (i : FolkmanFiniteCodeEmbedding S.atom B),
    ∃ (gL : AsBoolRing (Finset (Fin B.leftCount)) →ₙ+* L)
      (gR : AsBoolRing (Finset (Fin B.rightCount)) →ₙ+* R),
      Function.Injective gL ∧
      Function.Injective gR ∧
      (∀ (s : Finset (Fin B.leftCount))
          (t : Finset (Fin B.rightCount)),
          β (gL (toBoolRing s)) (gR (toBoolRing t)) =
            ∑ a ∈ s, ∑ b ∈ t, B.edge a b) ∧
      (∀ x, gL (i.left x) = S.left x) ∧
      (∀ y, gR (i.right y) = S.right y)

/-- Finite source hull plus genuine embedding extension provides
a larger paired bridge. Its source copy is exactly the chosen
finite hull stage, so all points of that hull are in the new
source image. No use of a unit in either ambient sort. -/
theorem FolkmanFiniteCodeEPP.extend_source_hull
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (EPP : FolkmanFiniteCodeEPP L R β)
    (P : FolkmanFinitePairedBridge L R β)
    (H : FolkmanPairedBridgeSourceHull P) :
    ∃ Q : FolkmanFinitePairedBridge L R β,
      P ≤ Q ∧
      (∀ x : L, (∃ a, H.stage.left a = x) →
        ∃ a, Q.source.left a = x) ∧
      (∀ y : R, (∃ b, H.stage.right b = y) →
        ∃ b, Q.source.right b = y) := by
  classical
  obtain ⟨gL, gR, hgL, hgR, hPair, hL, hR⟩ :=
    EPP.extend P.swap.source H.stage.atom H.embedding
  let Q : FolkmanFinitePairedBridge L R β := {
    source := H.stage
    targetLeft := gL
    targetRight := gR
    targetLeft_injective := hgL
    targetRight_injective := hgR
    target_pairing := hPair
  }
  have hPQ : P ≤ Q := by
    refine ⟨{
      left := H.embedding.left
      right := H.embedding.right
      left_injective := H.embedding.left_injective
      right_injective := H.embedding.right_injective
      source_left_comm := H.left_commutes
      target_left_comm := hL
      source_right_comm := H.right_commutes
      target_right_comm := hR
    }⟩
  refine ⟨Q, hPQ, ?_, ?_⟩
  · intro x hx
    exact hx
  · intro y hy
    exact hy

/-- Source-left and source-right one-point bridge extensions follow
from ordinary finite EPP and finite hulls, not from an independent
back-and-forth assumption. -/
def folkmanFinitePairedBridgeForth_of_hulls_EPP
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (Hulls : FolkmanPairedBridgeSourceHullProperty L R β)
    (EPP : FolkmanFiniteCodeEPP L R β) :
    FolkmanFinitePairedBridgeForthExtension L R β where
  sourceLeft := by
    intro P x
    obtain ⟨H, a, ha⟩ := Hulls.left P x
    obtain ⟨Q, hPQ, hL, hR⟩ := EPP.extend_source_hull P H
    exact ⟨Q, hPQ, hL x ⟨a, ha⟩⟩
  sourceRight := by
    intro P y
    obtain ⟨H, b, hb⟩ := Hulls.right P y
    obtain ⟨Q, hPQ, hL, hR⟩ := EPP.extend_source_hull P H
    exact ⟨Q, hPQ, hR y ⟨b, hb⟩⟩

/-- Conditional generated homogeneity with the standard, checkable
finite hull and finite embedding-extension properties as inputs.
Constructing the countable Folkman limit and these inputs remains. -/
theorem folkmanGeneratedHomogeneous_of_hulls_EPP
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (Hulls : FolkmanPairedBridgeSourceHullProperty L R β)
    (EPP : FolkmanFiniteCodeEPP L R β) :
    FolkmanGeneratedHomogeneous L R β :=
  folkmanGeneratedHomogeneous_of_atlas_forth A
    (folkmanFinitePairedBridgeForth_of_hulls_EPP Hulls EPP)

/-- Under finite hulls and EPP, equality of the complete finite
two-sort profile is equivalent to the action of a *genuine* global
pairing-preserving automorphism. Neither a spurious group action
nor a separate homogeneity axiom occurs in the conclusion. -/
theorem folkmanGlobalTupleRelated_iff_profile_eq_of_hulls_EPP
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (Hulls : FolkmanPairedBridgeSourceHullProperty L R β)
    (EPP : FolkmanFiniteCodeEPP L R β)
    {nL nR : ℕ}
    (p q : (Fin nL → L) × (Fin nR → R)) :
    folkmanGlobalTupleRelated β p q ↔
      A.tupleProfile p.1 p.2 = A.tupleProfile q.1 q.2 :=
  folkmanGlobalTupleRelated_iff_profile_eq A
    (folkmanGeneratedHomogeneous_of_hulls_EPP A Hulls EPP) p q

/-- The same exact profile classification for arbitrary mixed-sort
tuples, retaining their original sort labels. -/
theorem folkmanGlobalTaggedRelated_iff_profile_eq_of_hulls_EPP
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (Hulls : FolkmanPairedBridgeSourceHullProperty L R β)
    (EPP : FolkmanFiniteCodeEPP L R β)
    {n : ℕ}
    (p q : FolkmanTaggedStageTuple L R n) :
    folkmanGlobalTaggedRelated β p q ↔
      A.taggedProfile p = A.taggedProfile q :=
  folkmanGlobalTaggedRelated_iff_profile_eq A
    (folkmanGeneratedHomogeneous_of_hulls_EPP A Hulls EPP) p q

/-- Finite genuine two-sort global orbit quotients, conditional
on finite hulls and the ordinary finite EPP of the ambient model. -/
theorem folkmanGlobalTupleOrbits_finite_of_hulls_EPP
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (Hulls : FolkmanPairedBridgeSourceHullProperty L R β)
    (EPP : FolkmanFiniteCodeEPP L R β)
    (nL nR : ℕ) :
    Finite (Quotient (folkmanGlobalTupleSetoid β nL nR)) :=
  folkmanGlobalTupleOrbits_finite_of_generatedHomogeneity A
    (folkmanGeneratedHomogeneous_of_hulls_EPP A Hulls EPP) nL nR

/-- Finite genuine mixed-sort global automorphism orbits under
exactly the same two finite extension/hull hypotheses. -/
theorem folkmanGlobalTaggedOrbits_finite_of_hulls_EPP
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    [Countable L] [Countable R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (Hulls : FolkmanPairedBridgeSourceHullProperty L R β)
    (EPP : FolkmanFiniteCodeEPP L R β)
    (n : ℕ) :
    Finite (Quotient (folkmanGlobalTaggedSetoid β n)) :=
  folkmanGlobalTaggedOrbits_finite_of_generatedHomogeneity A
    (folkmanGeneratedHomogeneous_of_hulls_EPP A Hulls EPP) n


end SuccessorTree.NonPrecompact
