import BANANA.NonPrecompact.BananaTriplePairing

/-!
# Equivariant redundant triple amalgams of BANANA pairings

Given A → B and A → C, compatible automorphisms F_A, F_B, F_C
act componentwise on the redundant coordinate space A ⊕ B ⊕ C.
The pulled-back B- and C-pairings, with the A-pairing subtracted once,
are invariant under these actions.

This is the algebraic first step in constructing a perfect-total
amalgam of arbitrary finite systems of automorphisms. We deliberately
do not assert that the redundant ambient pairing is perfect, or that
these actions already intertwine the embeddings of B and C: the latter
requires equivariant retractions. Perfect completion and system
amalgamation are subsequent tasks.
-/

namespace SuccessorTree.NonPrecompact

/-- Componentwise linear action in redundant triple coordinates. -/
def bananaTripleLinearAction {a b c : ℕ}
    (p : (Fin a → F2) →ₗ[F2] (Fin a → F2))
    (q : (Fin b → F2) →ₗ[F2] (Fin b → F2))
    (r : (Fin c → F2) →ₗ[F2] (Fin c → F2)) :
    (Fin ((a + b) + c) → F2) →ₗ[F2]
      (Fin ((a + b) + c) → F2) :=
  BananaMatrixStructure.directSumLinearMap
    (BananaMatrixStructure.directSumLinearMap p q) r

/-- The shared A-coordinate transforms by its own action. -/
@[simp] theorem tripleProjA_bananaTripleLinearAction
    {a b c : ℕ}
    (p : (Fin a → F2) →ₗ[F2] (Fin a → F2))
    (q : (Fin b → F2) →ₗ[F2] (Fin b → F2))
    (r : (Fin c → F2) →ₗ[F2] (Fin c → F2))
    (x : Fin ((a + b) + c) → F2) :
    tripleProjA (bananaTripleLinearAction p q r x) =
      p (tripleProjA x) := by
  change BananaMatrixStructure.finLeftPart
      (BananaMatrixStructure.finLeftPart
        (bananaTripleLinearAction p q r x)) =
    p (BananaMatrixStructure.finLeftPart
      (BananaMatrixStructure.finLeftPart x))
  simp only [bananaTripleLinearAction,
    BananaMatrixStructure.finLeftPart_directSumLinearMap]

/-- The B-coordinate transforms by its own action. -/
@[simp] theorem tripleProjB_bananaTripleLinearAction
    {a b c : ℕ}
    (p : (Fin a → F2) →ₗ[F2] (Fin a → F2))
    (q : (Fin b → F2) →ₗ[F2] (Fin b → F2))
    (r : (Fin c → F2) →ₗ[F2] (Fin c → F2))
    (x : Fin ((a + b) + c) → F2) :
    tripleProjB (bananaTripleLinearAction p q r x) =
      q (tripleProjB x) := by
  change BananaMatrixStructure.finRightPart
      (BananaMatrixStructure.finLeftPart
        (bananaTripleLinearAction p q r x)) =
    q (BananaMatrixStructure.finRightPart
      (BananaMatrixStructure.finLeftPart x))
  simp only [bananaTripleLinearAction,
    BananaMatrixStructure.finLeftPart_directSumLinearMap,
    BananaMatrixStructure.finRightPart_directSumLinearMap]

/-- The C-coordinate transforms by its own action. -/
@[simp] theorem tripleProjC_bananaTripleLinearAction
    {a b c : ℕ}
    (p : (Fin a → F2) →ₗ[F2] (Fin a → F2))
    (q : (Fin b → F2) →ₗ[F2] (Fin b → F2))
    (r : (Fin c → F2) →ₗ[F2] (Fin c → F2))
    (x : Fin ((a + b) + c) → F2) :
    tripleProjC (bananaTripleLinearAction p q r x) =
      r (tripleProjC x) := by
  change BananaMatrixStructure.finRightPart
      (bananaTripleLinearAction p q r x) =
    r (BananaMatrixStructure.finRightPart x)
  simp only [bananaTripleLinearAction,
    BananaMatrixStructure.finRightPart_directSumLinearMap]

/-- The B-pullback is equivariant whenever the B-action
intertwines the embedding from A. -/
theorem triplePullbackB_bananaTripleLinearAction
    {a b c : ℕ}
    (f : (Fin a → F2) →ₗ[F2] (Fin b → F2))
    (p : (Fin a → F2) →ₗ[F2] (Fin a → F2))
    (q : (Fin b → F2) →ₗ[F2] (Fin b → F2))
    (r : (Fin c → F2) →ₗ[F2] (Fin c → F2))
    (h : ∀ a, q (f a) = f (p a))
    (x : Fin ((a + b) + c) → F2) :
    (triplePullbackB (c := c) f)
        (bananaTripleLinearAction p q r x) =
      q ((triplePullbackB (c := c) f) x) := by
  change f (tripleProjA (bananaTripleLinearAction p q r x)) +
      tripleProjB (bananaTripleLinearAction p q r x) =
    q (f (tripleProjA x) + tripleProjB x)
  rw [tripleProjA_bananaTripleLinearAction,
    tripleProjB_bananaTripleLinearAction, map_add]
  rw [← h (tripleProjA x)]

/-- The analogous C-pullback is equivariant. -/
theorem triplePullbackC_bananaTripleLinearAction
    {a b c : ℕ}
    (g : (Fin a → F2) →ₗ[F2] (Fin c → F2))
    (p : (Fin a → F2) →ₗ[F2] (Fin a → F2))
    (q : (Fin b → F2) →ₗ[F2] (Fin b → F2))
    (r : (Fin c → F2) →ₗ[F2] (Fin c → F2))
    (h : ∀ a, r (g a) = g (p a))
    (x : Fin ((a + b) + c) → F2) :
    (triplePullbackC (b := b) g)
        (bananaTripleLinearAction p q r x) =
      r ((triplePullbackC (b := b) g) x) := by
  change g (tripleProjA (bananaTripleLinearAction p q r x)) +
      tripleProjC (bananaTripleLinearAction p q r x) =
    r (g (tripleProjA x) + tripleProjC x)
  rw [tripleProjA_bananaTripleLinearAction,
    tripleProjC_bananaTripleLinearAction, map_add]
  rw [← h (tripleProjA x)]

/-- Compatible componentwise self-embeddings preserve the bilinear
pairing on the redundant amalgam. No nondegeneracy is assumed. -/
theorem bananaTripleLinearAction_preserves_pairing
    {aL aR bL bR cL cR : ℕ}
    (A : BananaMatrixStructure aL aR)
    (B : BananaMatrixStructure bL bR)
    (C : BananaMatrixStructure cL cR)
    (f : BananaMatrixEmbedding A B)
    (g : BananaMatrixEmbedding A C)
    (FA : BananaMatrixEmbedding A A)
    (FB : BananaMatrixEmbedding B B)
    (FC : BananaMatrixEmbedding C C)
    (hBL : ∀ x, FB.left (f.left x) = f.left (FA.left x))
    (hBR : ∀ y, FB.right (f.right y) = f.right (FA.right y))
    (hCL : ∀ x, FC.left (g.left x) = g.left (FA.left x))
    (hCR : ∀ y, FC.right (g.right y) = g.right (FA.right y))
    (x : Fin ((aL + bL) + cL) → F2)
    (y : Fin ((aR + bR) + cR) → F2) :
    (bananaTripleAmalgam A B C f g).eval
      (bananaTripleLinearAction FA.left FB.left FC.left x)
      (bananaTripleLinearAction FA.right FB.right FC.right y) =
    (bananaTripleAmalgam A B C f g).eval x y := by
  simp only [bananaTripleAmalgam_eval]
  rw [triplePullbackB_bananaTripleLinearAction
      f.left FA.left FB.left FC.left hBL x,
    triplePullbackB_bananaTripleLinearAction
      f.right FA.right FB.right FC.right hBR y,
    triplePullbackC_bananaTripleLinearAction
      g.left FA.left FB.left FC.left hCL x,
    triplePullbackC_bananaTripleLinearAction
      g.right FA.right FB.right FC.right hCR y,
    tripleProjA_bananaTripleLinearAction,
    tripleProjA_bananaTripleLinearAction,
    FB.pairing_apply,
    FC.pairing_apply,
    FA.pairing_apply]

/-- A genuine self-embedding of the redundant amalgam, induced by
three compatible automorphisms of the original systems. -/
def bananaTripleAmalgamAutomorphism
    {aL aR bL bR cL cR : ℕ}
    (A : BananaMatrixStructure aL aR)
    (B : BananaMatrixStructure bL bR)
    (C : BananaMatrixStructure cL cR)
    (f : BananaMatrixEmbedding A B)
    (g : BananaMatrixEmbedding A C)
    (FA : BananaMatrixEmbedding A A)
    (FB : BananaMatrixEmbedding B B)
    (FC : BananaMatrixEmbedding C C)
    (hBL : ∀ x, FB.left (f.left x) = f.left (FA.left x))
    (hBR : ∀ y, FB.right (f.right y) = f.right (FA.right y))
    (hCL : ∀ x, FC.left (g.left x) = g.left (FA.left x))
    (hCR : ∀ y, FC.right (g.right y) = g.right (FA.right y)) :
    BananaMatrixEmbedding (bananaTripleAmalgam A B C f g)
      (bananaTripleAmalgam A B C f g) where
  left := bananaTripleLinearAction FA.left FB.left FC.left
  right := bananaTripleLinearAction FA.right FB.right FC.right
  left_injective :=
    BananaMatrixStructure.directSumLinearMap_injective
      (BananaMatrixStructure.directSumLinearMap_injective
        FA.left_injective FB.left_injective) FC.left_injective
  right_injective :=
    BananaMatrixStructure.directSumLinearMap_injective
      (BananaMatrixStructure.directSumLinearMap_injective
        FA.right_injective FB.right_injective) FC.right_injective
  pairing_apply := by
    intro x y
    exact bananaTripleLinearAction_preserves_pairing
      A B C f g FA FB FC hBL hBR hCL hCR x y

end SuccessorTree.NonPrecompact
