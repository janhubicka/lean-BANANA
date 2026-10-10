import BANANA.NonPrecompact.BananaEquivariantTripleAmalgam
import BANANA.NonPrecompact.BananaPerfectProjectionEquivariance

/-!
# Canonically equivariant embeddings in the perfect-total diagram amalgam

For a diagram of finite *perfect* BANANA pairings A ↪ B,C, use
the canonical pairing retractions (rather than arbitrary linear
complements) in the redundant triple-coordinate amalgam.

These retractions commute with every compatible named automorphism.
Consequently the two actual embeddings B,C ↪ D intertwine the
componentwise automorphisms of D simultaneously for every name.

The ambient D is an arbitrary finite pairing. Completing D to a
perfect pairing with compatible total actions is the next step.
No assertion about WAP or ample generics is made here.
-/

namespace SuccessorTree.NonPrecompact

/-- The three coordinate projections jointly separate vectors in
a redundant triple-coordinate space. -/
theorem bananaTriple_projection_ext {a b c : ℕ}
    {x y : Fin ((a + b) + c) → F2}
    (hA : tripleProjA x = tripleProjA y)
    (hB : tripleProjB x = tripleProjB y)
    (hC : tripleProjC x = tripleProjC y) :
    x = y := by
  funext i
  induction i using Fin.addCases with
  | left j =>
      induction j using Fin.addCases with
      | left k =>
          have hk := congrFun hA k
          simpa [tripleProjA, finLeftPartLinear,
            BananaMatrixStructure.finLeftPart] using hk
      | right k =>
          have hk := congrFun hB k
          simpa [tripleProjB, finLeftPartLinear, finRightPartLinear,
            BananaMatrixStructure.finLeftPart,
            BananaMatrixStructure.finRightPart] using hk
  | right k =>
      have hk := congrFun hC k
      simpa [tripleProjC, finRightPartLinear,
        BananaMatrixStructure.finRightPart] using hk

/-- A redundant B-inclusion is equivariant provided the selected
retraction commutes with the source and ambient actions. -/
theorem bananaTripleInl_equivariant
    {a b c : ℕ}
    (f : (Fin a → F2) →ₗ[F2] (Fin b → F2))
    (pr : (Fin b → F2) →ₗ[F2] (Fin a → F2))
    (p : (Fin a → F2) →ₗ[F2] (Fin a → F2))
    (q : (Fin b → F2) →ₗ[F2] (Fin b → F2))
    (r : (Fin c → F2) →ₗ[F2] (Fin c → F2))
    (hf : ∀ z, q (f z) = f (p z))
    (hpr : ∀ z, pr (q z) = p (pr z))
    (x : Fin b → F2) :
    bananaTripleLinearAction p q r
        (tripleInl (c := c) f pr x) =
      tripleInl (c := c) f pr (q x) := by
  apply bananaTriple_projection_ext
  · rw [tripleProjA_bananaTripleLinearAction,
      tripleProjA_inl, tripleProjA_inl]
    exact (hpr x).symm
  · rw [tripleProjB_bananaTripleLinearAction,
      tripleProjB_inl, tripleProjB_inl, map_sub, hf (pr x)]
    rw [hpr x]
  · rw [tripleProjC_bananaTripleLinearAction,
      tripleProjC_inl, tripleProjC_inl, map_zero]

/-- A redundant C-inclusion is equivariant with its own canonical
retraction. -/
theorem bananaTripleInr_equivariant
    {a b c : ℕ}
    (g : (Fin a → F2) →ₗ[F2] (Fin c → F2))
    (pr : (Fin c → F2) →ₗ[F2] (Fin a → F2))
    (p : (Fin a → F2) →ₗ[F2] (Fin a → F2))
    (q : (Fin b → F2) →ₗ[F2] (Fin b → F2))
    (r : (Fin c → F2) →ₗ[F2] (Fin c → F2))
    (hg : ∀ z, r (g z) = g (p z))
    (hpr : ∀ z, pr (r z) = p (pr z))
    (x : Fin c → F2) :
    bananaTripleLinearAction p q r
        (tripleInr (b := b) g pr x) =
      tripleInr (b := b) g pr (r x) := by
  apply bananaTriple_projection_ext
  · rw [tripleProjA_bananaTripleLinearAction,
      tripleProjA_inr, tripleProjA_inr]
    exact (hpr x).symm
  · rw [tripleProjB_bananaTripleLinearAction,
      tripleProjB_inr, tripleProjB_inr, map_zero]
  · rw [tripleProjC_bananaTripleLinearAction,
      tripleProjC_inr, tripleProjC_inr, map_sub, hg (pr x)]
    rw [hpr x]

/-- Every finite family of compatible automorphisms of an arbitrary
perfect diagram A ↪ B,C simultaneously acts on a common finite
BANANA amalgam, and the *actual* embeddings of B and C commute
with all named automorphisms on both sorts. -/
theorem exists_bananaPerfectTotalSystem_redundant_amalgam
    {n a b c : ℕ}
    (f : BananaMatrixEmbedding (perfectBanana a) (perfectBanana b))
    (g : BananaMatrixEmbedding (perfectBanana a) (perfectBanana c))
    (FA : Fin n → BananaMatrixEmbedding (perfectBanana a) (perfectBanana a))
    (FB : Fin n → BananaMatrixEmbedding (perfectBanana b) (perfectBanana b))
    (FC : Fin n → BananaMatrixEmbedding (perfectBanana c) (perfectBanana c))
    (hBL : ∀ i x, (FB i).left (f.left x) = f.left ((FA i).left x))
    (hBR : ∀ i y, (FB i).right (f.right y) = f.right ((FA i).right y))
    (hCL : ∀ i x, (FC i).left (g.left x) = g.left ((FA i).left x))
    (hCR : ∀ i y, (FC i).right (g.right y) = g.right ((FA i).right y)) :
    ∃ D : BananaMatrixStructure ((a + b) + c) ((a + b) + c),
    ∃ eB : BananaMatrixEmbedding (perfectBanana b) D,
    ∃ eC : BananaMatrixEmbedding (perfectBanana c) D,
    ∃ HD : Fin n → BananaMatrixEmbedding D D,
      (∀ x, eB.left (f.left x) = eC.left (g.left x)) ∧
      (∀ y, eB.right (f.right y) = eC.right (g.right y)) ∧
      (∀ i x, (HD i).left (eB.left x) = eB.left ((FB i).left x)) ∧
      (∀ i y, (HD i).right (eB.right y) = eB.right ((FB i).right y)) ∧
      (∀ i x, (HD i).left (eC.left x) = eC.left ((FC i).left x)) ∧
      (∀ i y, (HD i).right (eC.right y) = eC.right ((FC i).right y)) := by
  let A := perfectBanana a
  let B := perfectBanana b
  let C := perfectBanana c
  let pBL := rightPairingMap f
  let pBR := perfectLeftPairingMap f
  let pCL := rightPairingMap g
  let pCR := perfectLeftPairingMap g
  let D := bananaTripleAmalgam A B C f g
  let eB : BananaMatrixEmbedding B D :=
    bananaTripleAmalgamInl A B C f g pBL pBR
  let eC : BananaMatrixEmbedding C D :=
    bananaTripleAmalgamInr A B C f g pCL pCR
  let HD : Fin n → BananaMatrixEmbedding D D :=
    fun i => bananaTripleAmalgamAutomorphism
      A B C f g (FA i) (FB i) (FC i)
        (hBL i) (hBR i) (hCL i) (hCR i)
  refine ⟨D, eB, eC, HD, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change tripleInl f.left pBL (f.left x) =
      tripleInr g.left pCL (g.left x)
    exact tripleInl_comp_eq_tripleInr_comp
      f.left g.left pBL pCL
      (rightPairingMap_left_retraction f)
      (rightPairingMap_left_retraction g) x
  · intro y
    change tripleInl f.right pBR (f.right y) =
      tripleInr g.right pCR (g.right y)
    exact tripleInl_comp_eq_tripleInr_comp
      f.right g.right pBR pCR
      (perfectLeftPairingMap_right_retraction f)
      (perfectLeftPairingMap_right_retraction g) y
  · intro i x
    change bananaTripleLinearAction
        (FA i).left (FB i).left (FC i).left
          (tripleInl f.left pBL x) =
        tripleInl f.left pBL ((FB i).left x)
    exact bananaTripleInl_equivariant
      f.left pBL (FA i).left (FB i).left (FC i).left
      (hBL i)
      (rightPairingMap_intertwines_perfectTotal
        f (FA i) (FB i) (hBL i) (hBR i)) x
  · intro i y
    change bananaTripleLinearAction
        (FA i).right (FB i).right (FC i).right
          (tripleInl f.right pBR y) =
        tripleInl f.right pBR ((FB i).right y)
    exact bananaTripleInl_equivariant
      f.right pBR (FA i).right (FB i).right (FC i).right
      (hBR i)
      (perfectLeftPairingMap_intertwines_perfectTotal
        f (FA i) (FB i) (hBL i) (hBR i)) y
  · intro i x
    change bananaTripleLinearAction
        (FA i).left (FB i).left (FC i).left
          (tripleInr g.left pCL x) =
        tripleInr g.left pCL ((FC i).left x)
    exact bananaTripleInr_equivariant
      g.left pCL (FA i).left (FB i).left (FC i).left
      (hCL i)
      (rightPairingMap_intertwines_perfectTotal
        g (FA i) (FC i) (hCL i) (hCR i)) x
  · intro i y
    change bananaTripleLinearAction
        (FA i).right (FB i).right (FC i).right
          (tripleInr g.right pCR y) =
        tripleInr g.right pCR ((FC i).right y)
    exact bananaTripleInr_equivariant
      g.right pCR (FA i).right (FB i).right (FC i).right
      (hCR i)
      (perfectLeftPairingMap_intertwines_perfectTotal
        g (FA i) (FC i) (hCL i) (hCR i)) y

end SuccessorTree.NonPrecompact
