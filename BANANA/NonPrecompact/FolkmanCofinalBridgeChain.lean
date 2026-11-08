import BANANA.NonPrecompact.FolkmanGlobalPairAutomorphismOrbits

/-!
# Cofinal finite two-sort bridges for Folkman back-and-forth

A bridge is a finite atom-coded Folkman object embedded twice in
one non-unital ambient pairing. We retain the source and target maps
on both sorts and require that the two copies carry exactly the same
pairing on every finite stage element.

An exhaustive coherent chain is more data than a directed atlas:
every ambient element must occur on both sides of the chain, and
refining two finite stages must preserve their source and target
images simultaneously. The explicit coherence and common-stage
fields below are the exact inputs to the generic back-and-forth
limit. Constructing such a chain from finite extension properties
is a *separate* obligation and is not silently assumed here.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- An exhaustive family of common finite atom presentations,
embedded twice in the original two-sort non-unital pairing.

We use the named ring operations only: zero, addition and
multiplication. No ambient unit is required, even though the finite
atom presentation has an intrinsic greatest element. -/
structure FolkmanCofinalBridgeChain
    (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) where
  code : ℕ → FolkmanAtomStructure
  sourceLeft : (n : ℕ) →
    AsBoolRing (Finset (Fin (code n).leftCount)) →ₙ+* L
  targetLeft : (n : ℕ) →
    AsBoolRing (Finset (Fin (code n).leftCount)) →ₙ+* L
  sourceRight : (n : ℕ) →
    AsBoolRing (Finset (Fin (code n).rightCount)) →ₙ+* R
  targetRight : (n : ℕ) →
    AsBoolRing (Finset (Fin (code n).rightCount)) →ₙ+* R
  sourceLeft_injective : ∀ n, Function.Injective (sourceLeft n)
  targetLeft_injective : ∀ n, Function.Injective (targetLeft n)
  sourceRight_injective : ∀ n, Function.Injective (sourceRight n)
  targetRight_injective : ∀ n, Function.Injective (targetRight n)
  source_stage_pairing : ∀ n
      (a : AsBoolRing (Finset (Fin (code n).leftCount)))
      (b : AsBoolRing (Finset (Fin (code n).rightCount))),
      β (sourceLeft n a) (sourceRight n b) =
        ∑ i ∈ ofBoolRing a, ∑ j ∈ ofBoolRing b, (code n).edge i j
  target_stage_pairing : ∀ n
      (a : AsBoolRing (Finset (Fin (code n).leftCount)))
      (b : AsBoolRing (Finset (Fin (code n).rightCount))),
      β (targetLeft n a) (targetRight n b) =
        ∑ i ∈ ofBoolRing a, ∑ j ∈ ofBoolRing b, (code n).edge i j
  left_forward_coherent : ∀ n m
      (a : AsBoolRing (Finset (Fin (code n).leftCount)))
      (b : AsBoolRing (Finset (Fin (code m).leftCount))),
      sourceLeft n a = sourceLeft m b →
        targetLeft n a = targetLeft m b
  left_backward_coherent : ∀ n m
      (a : AsBoolRing (Finset (Fin (code n).leftCount)))
      (b : AsBoolRing (Finset (Fin (code m).leftCount))),
      targetLeft n a = targetLeft m b →
        sourceLeft n a = sourceLeft m b
  right_forward_coherent : ∀ n m
      (a : AsBoolRing (Finset (Fin (code n).rightCount)))
      (b : AsBoolRing (Finset (Fin (code m).rightCount))),
      sourceRight n a = sourceRight m b →
        targetRight n a = targetRight m b
  right_backward_coherent : ∀ n m
      (a : AsBoolRing (Finset (Fin (code n).rightCount)))
      (b : AsBoolRing (Finset (Fin (code m).rightCount))),
      targetRight n a = targetRight m b →
        sourceRight n a = sourceRight m b
  commonLeft : ∀ n m
      (a : AsBoolRing (Finset (Fin (code n).leftCount)))
      (b : AsBoolRing (Finset (Fin (code m).leftCount))),
      ∃ k (u v : AsBoolRing (Finset (Fin (code k).leftCount))),
        sourceLeft k u = sourceLeft n a ∧
        targetLeft k u = targetLeft n a ∧
        sourceLeft k v = sourceLeft m b ∧
        targetLeft k v = targetLeft m b
  commonRight : ∀ n m
      (a : AsBoolRing (Finset (Fin (code n).rightCount)))
      (b : AsBoolRing (Finset (Fin (code m).rightCount))),
      ∃ k (u v : AsBoolRing (Finset (Fin (code k).rightCount))),
        sourceRight k u = sourceRight n a ∧
        targetRight k u = targetRight n a ∧
        sourceRight k v = sourceRight m b ∧
        targetRight k v = targetRight m b
  commonPair : ∀ n m
      (a : AsBoolRing (Finset (Fin (code n).leftCount)))
      (b : AsBoolRing (Finset (Fin (code m).rightCount))),
      ∃ k
        (u : AsBoolRing (Finset (Fin (code k).leftCount)))
        (v : AsBoolRing (Finset (Fin (code k).rightCount))),
        sourceLeft k u = sourceLeft n a ∧
        targetLeft k u = targetLeft n a ∧
        sourceRight k v = sourceRight m b ∧
        targetRight k v = targetRight m b
  sourceLeft_exhaustive : ∀ x : L,
    ∃ n, ∃ a, sourceLeft n a = x
  targetLeft_exhaustive : ∀ x : L,
    ∃ n, ∃ a, targetLeft n a = x
  sourceRight_exhaustive : ∀ y : R,
    ∃ n, ∃ b, sourceRight n b = y
  targetRight_exhaustive : ∀ y : R,
    ∃ n, ∃ b, targetRight n b = y

namespace FolkmanCofinalBridgeChain

variable {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
variable {β : L → R → F2}

/-- Both bridge images reconstruct the *same* actual finite atom
matrix on every input. This equality follows from their respective
faithful pairing certificates, rather than being postulated. -/
theorem stage_pairing (C : FolkmanCofinalBridgeChain L R β)
    (n : ℕ)
    (a : AsBoolRing (Finset (Fin (C.code n).leftCount)))
    (b : AsBoolRing (Finset (Fin (C.code n).rightCount))) :
    β (C.sourceLeft n a) (C.sourceRight n b) =
      β (C.targetLeft n a) (C.targetRight n b) :=
  (C.source_stage_pairing n a b).trans
    (C.target_stage_pairing n a b).symm

/-- Choose a source finite-stage representative of one left element. -/
noncomputable def chooseLeft (C : FolkmanCofinalBridgeChain L R β)
    (x : L) :
    Σ n : ℕ, AsBoolRing (Finset (Fin (C.code n).leftCount)) :=
  ⟨Classical.choose (C.sourceLeft_exhaustive x),
    Classical.choose (Classical.choose_spec (C.sourceLeft_exhaustive x))⟩

/-- The chosen left representative really represents the element. -/
theorem chooseLeft_spec (C : FolkmanCofinalBridgeChain L R β)
    (x : L) :
    C.sourceLeft (C.chooseLeft x).1 (C.chooseLeft x).2 = x :=
  Classical.choose_spec (Classical.choose_spec (C.sourceLeft_exhaustive x))

/-- Choose a source finite-stage representative of one right element. -/
noncomputable def chooseRight (C : FolkmanCofinalBridgeChain L R β)
    (y : R) :
    Σ n : ℕ, AsBoolRing (Finset (Fin (C.code n).rightCount)) :=
  ⟨Classical.choose (C.sourceRight_exhaustive y),
    Classical.choose (Classical.choose_spec (C.sourceRight_exhaustive y))⟩

theorem chooseRight_spec (C : FolkmanCofinalBridgeChain L R β)
    (y : R) :
    C.sourceRight (C.chooseRight y).1 (C.chooseRight y).2 = y :=
  Classical.choose_spec (Classical.choose_spec (C.sourceRight_exhaustive y))

/-- The forward map sends a source-stage representative to its
corresponding target-stage element. -/
noncomputable def forwardLeft (C : FolkmanCofinalBridgeChain L R β)
    (x : L) : L :=
  let w := C.chooseLeft x
  C.targetLeft w.1 w.2

noncomputable def forwardRight (C : FolkmanCofinalBridgeChain L R β)
    (y : R) : R :=
  let w := C.chooseRight y
  C.targetRight w.1 w.2

/-- The choice of representative does not change the forward left map. -/
theorem forwardLeft_on_stage (C : FolkmanCofinalBridgeChain L R β)
    (n : ℕ)
    (a : AsBoolRing (Finset (Fin (C.code n).leftCount))) :
    C.forwardLeft (C.sourceLeft n a) = C.targetLeft n a := by
  let w := C.chooseLeft (C.sourceLeft n a)
  have hw : C.sourceLeft w.1 w.2 = C.sourceLeft n a :=
    C.chooseLeft_spec _
  exact C.left_forward_coherent w.1 n w.2 a hw

/-- The corresponding choice-independent right map. -/
theorem forwardRight_on_stage (C : FolkmanCofinalBridgeChain L R β)
    (n : ℕ)
    (a : AsBoolRing (Finset (Fin (C.code n).rightCount))) :
    C.forwardRight (C.sourceRight n a) = C.targetRight n a := by
  let w := C.chooseRight (C.sourceRight n a)
  have hw : C.sourceRight w.1 w.2 = C.sourceRight n a :=
    C.chooseRight_spec _
  exact C.right_forward_coherent w.1 n w.2 a hw

end FolkmanCofinalBridgeChain
end SuccessorTree.NonPrecompact
