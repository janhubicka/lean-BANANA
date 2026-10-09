import BANANA.NonPrecompact.BananaTripleIntersection

/-!
# Arbitrary strong amalgamation of finite BANANA pairings

We construct the amalgam of arbitrary embeddings f : A → B, g : A → C
in the redundant coordinate space A ⊕ B ⊕ C. Choose linear
retractions on each sort. The B- and C-images agree on A and have
exactly its image as their intersection by BananaTripleIntersection.

To preserve the pairings, evaluate the old B- and C-pairings through
the maps (a,u,v) ↦ f(a)+u and (a,u,v) ↦ g(a)+v, then subtract the
common A-pairing once. This is a bilinear form for any finite field
and requires no nondegeneracy assumptions.
-/

namespace SuccessorTree.NonPrecompact

/-- Map a triple-coordinate vector to the B-sort by adding the
common component mapped through f to its B-only remainder. -/
def triplePullbackB
    {a b c : ℕ}
    (f : (Fin a → F2) →ₗ[F2] (Fin b → F2)) :
    (Fin ((a + b) + c) → F2) →ₗ[F2] (Fin b → F2) :=
  f.comp tripleProjA + tripleProjB

/-- The analogous map to the C-sort. -/
def triplePullbackC
    {a b c : ℕ}
    (g : (Fin a → F2) →ₗ[F2] (Fin c → F2)) :
    (Fin ((a + b) + c) → F2) →ₗ[F2] (Fin c → F2) :=
  g.comp tripleProjA + tripleProjC

theorem triplePullbackB_inl
    {a b c : ℕ}
    (f : (Fin a → F2) →ₗ[F2] (Fin b → F2))
    (p : (Fin b → F2) →ₗ[F2] (Fin a → F2))
    (x : Fin b → F2) :
    (triplePullbackB (c := c) f) (tripleInl (c := c) f p x) = x := by
  change f (tripleProjA (tripleInl f p x)) +
    tripleProjB (tripleInl f p x) = x
  rw [tripleProjA_inl, tripleProjB_inl]
  abel

theorem triplePullbackC_inl
    {a b c : ℕ}
    (f : (Fin a → F2) →ₗ[F2] (Fin b → F2))
    (g : (Fin a → F2) →ₗ[F2] (Fin c → F2))
    (p : (Fin b → F2) →ₗ[F2] (Fin a → F2))
    (x : Fin b → F2) :
    (triplePullbackC (b := b) g) (tripleInl (c := c) f p x) = g (p x) := by
  change g (tripleProjA (tripleInl f p x)) +
    tripleProjC (tripleInl f p x) = g (p x)
  rw [tripleProjA_inl, tripleProjC_inl]
  simp

theorem triplePullbackB_inr
    {a b c : ℕ}
    (f : (Fin a → F2) →ₗ[F2] (Fin b → F2))
    (g : (Fin a → F2) →ₗ[F2] (Fin c → F2))
    (p : (Fin c → F2) →ₗ[F2] (Fin a → F2))
    (x : Fin c → F2) :
    (triplePullbackB (c := c) f) (tripleInr (b := b) g p x) = f (p x) := by
  change f (tripleProjA (tripleInr g p x)) +
    tripleProjB (tripleInr g p x) = f (p x)
  rw [tripleProjA_inr, tripleProjB_inr]
  simp

theorem triplePullbackC_inr
    {a b c : ℕ}
    (g : (Fin a → F2) →ₗ[F2] (Fin c → F2))
    (p : (Fin c → F2) →ₗ[F2] (Fin a → F2))
    (x : Fin c → F2) :
    (triplePullbackC (b := b) g) (tripleInr (b := b) g p x) = x := by
  change g (tripleProjA (tripleInr g p x)) +
    tripleProjC (tripleInr g p x) = x
  rw [tripleProjA_inr, tripleProjC_inr]
  abel

/-- Subtracting pairings is a pointwise difference of their
finite coefficient matrices. -/
def bananaPairingSub
    {l r : ℕ} (X Y : BananaMatrixStructure l r) :
    BananaMatrixStructure l r where
  pairing := X.pairing - Y.pairing

theorem bananaPairingSub_eval
    {l r : ℕ} (X Y : BananaMatrixStructure l r)
    (x : Fin l → F2) (y : Fin r → F2) :
    (bananaPairingSub X Y).eval x y = X.eval x y - Y.eval x y := by
  simp [bananaPairingSub, BananaMatrixStructure.eval,
    Matrix.sub_mulVec, dotProduct_sub]

/-- The bilinear pairing on the triple-coordinate amalgam.
The common A-pairing is subtracted to avoid double counting. -/
def bananaTripleAmalgam
    {aL aR bL bR cL cR : ℕ}
    (A : BananaMatrixStructure aL aR)
    (B : BananaMatrixStructure bL bR)
    (C : BananaMatrixStructure cL cR)
    (f : BananaMatrixEmbedding A B)
    (g : BananaMatrixEmbedding A C) :
    BananaMatrixStructure ((aL + bL) + cL) ((aR + bR) + cR) :=
  bananaPairingSub
    (bananaPairingAdd
      (bananaPairingPullback B
        (triplePullbackB (c := cL) f.left)
        (triplePullbackB (c := cR) f.right))
      (bananaPairingPullback C
        (triplePullbackC (b := bL) g.left)
        (triplePullbackC (b := bR) g.right)))
    (bananaPairingPullback A
      (tripleProjA (a := aL) (b := bL) (c := cL))
      (tripleProjA (a := aR) (b := bR) (c := cR)))

/-- The defining bilinear-form identity in terms of the three
pulled-back pairings. -/
theorem bananaTripleAmalgam_eval
    {aL aR bL bR cL cR : ℕ}
    (A : BananaMatrixStructure aL aR)
    (B : BananaMatrixStructure bL bR)
    (C : BananaMatrixStructure cL cR)
    (f : BananaMatrixEmbedding A B)
    (g : BananaMatrixEmbedding A C)
    (x : Fin ((aL + bL) + cL) → F2)
    (y : Fin ((aR + bR) + cR) → F2) :
    (bananaTripleAmalgam A B C f g).eval x y =
      B.eval (triplePullbackB (c := cL) f.left x)
        (triplePullbackB (c := cR) f.right y) +
      C.eval (triplePullbackC (b := bL) g.left x)
        (triplePullbackC (b := bR) g.right y) -
      A.eval (tripleProjA x) (tripleProjA y) := by
  simp only [bananaTripleAmalgam, bananaPairingSub_eval,
    bananaPairingAdd_eval, bananaPairingPullback_eval]

/-- The first redundant-coordinate inclusion preserves the
original B-pairing. This is independent of the choice of retractions. -/
theorem bananaTripleAmalgam_inl_pairing
    {aL aR bL bR cL cR : ℕ}
    (A : BananaMatrixStructure aL aR)
    (B : BananaMatrixStructure bL bR)
    (C : BananaMatrixStructure cL cR)
    (f : BananaMatrixEmbedding A B)
    (g : BananaMatrixEmbedding A C)
    (pL : (Fin bL → F2) →ₗ[F2] (Fin aL → F2))
    (pR : (Fin bR → F2) →ₗ[F2] (Fin aR → F2))
    (x : Fin bL → F2) (y : Fin bR → F2) :
    (bananaTripleAmalgam A B C f g).eval
      (tripleInl (c := cL) f.left pL x)
      (tripleInl (c := cR) f.right pR y) = B.eval x y := by
  rw [bananaTripleAmalgam_eval]
  rw [triplePullbackB_inl, triplePullbackB_inl,
    triplePullbackC_inl, triplePullbackC_inl,
    tripleProjA_inl, tripleProjA_inl]
  rw [g.pairing_apply]
  simp

/-- The second redundant-coordinate inclusion preserves the
original C-pairing. -/
theorem bananaTripleAmalgam_inr_pairing
    {aL aR bL bR cL cR : ℕ}
    (A : BananaMatrixStructure aL aR)
    (B : BananaMatrixStructure bL bR)
    (C : BananaMatrixStructure cL cR)
    (f : BananaMatrixEmbedding A B)
    (g : BananaMatrixEmbedding A C)
    (qL : (Fin cL → F2) →ₗ[F2] (Fin aL → F2))
    (qR : (Fin cR → F2) →ₗ[F2] (Fin aR → F2))
    (x : Fin cL → F2) (y : Fin cR → F2) :
    (bananaTripleAmalgam A B C f g).eval
      (tripleInr (b := bL) g.left qL x)
      (tripleInr (b := bR) g.right qR y) = C.eval x y := by
  rw [bananaTripleAmalgam_eval]
  rw [triplePullbackB_inr, triplePullbackB_inr,
    triplePullbackC_inr, triplePullbackC_inr,
    tripleProjA_inr, tripleProjA_inr]
  rw [f.pairing_apply]
  simp [add_comm, add_left_comm, add_assoc]

/-- The first structural BANANA embedding in the redundant amalgam. -/
def bananaTripleAmalgamInl
    {aL aR bL bR cL cR : ℕ}
    (A : BananaMatrixStructure aL aR)
    (B : BananaMatrixStructure bL bR)
    (C : BananaMatrixStructure cL cR)
    (f : BananaMatrixEmbedding A B)
    (g : BananaMatrixEmbedding A C)
    (pL : (Fin bL → F2) →ₗ[F2] (Fin aL → F2))
    (pR : (Fin bR → F2) →ₗ[F2] (Fin aR → F2)) :
    BananaMatrixEmbedding B (bananaTripleAmalgam A B C f g) where
  left := tripleInl (c := cL) f.left pL
  right := tripleInl (c := cR) f.right pR
  left_injective := tripleInl_injective f.left pL
  right_injective := tripleInl_injective f.right pR
  pairing_apply := bananaTripleAmalgam_inl_pairing A B C f g pL pR

/-- The second structural BANANA embedding in the redundant amalgam. -/
def bananaTripleAmalgamInr
    {aL aR bL bR cL cR : ℕ}
    (A : BananaMatrixStructure aL aR)
    (B : BananaMatrixStructure bL bR)
    (C : BananaMatrixStructure cL cR)
    (f : BananaMatrixEmbedding A B)
    (g : BananaMatrixEmbedding A C)
    (qL : (Fin cL → F2) →ₗ[F2] (Fin aL → F2))
    (qR : (Fin cR → F2) →ₗ[F2] (Fin aR → F2)) :
    BananaMatrixEmbedding C (bananaTripleAmalgam A B C f g) where
  left := tripleInr (b := bL) g.left qL
  right := tripleInr (b := bR) g.right qR
  left_injective := tripleInr_injective g.left qL
  right_injective := tripleInr_injective g.right qR
  pairing_apply := bananaTripleAmalgam_inr_pairing A B C f g qL qR

/-- Full strong amalgamation for arbitrary finite BANANA embeddings,
in a redundant but finite standard-coordinate ambient structure.
Both embeddings agree on A, and their images meet exactly in A on
each vector-space sort. -/
theorem BananaMatrixEmbedding.exists_strong_amalgam
    {aL aR bL bR cL cR : ℕ}
    {A : BananaMatrixStructure aL aR}
    {B : BananaMatrixStructure bL bR}
    {C : BananaMatrixStructure cL cR}
    (f : BananaMatrixEmbedding A B)
    (g : BananaMatrixEmbedding A C) :
    ∃ D : BananaMatrixStructure ((aL + bL) + cL) ((aR + bR) + cR),
    ∃ eB : BananaMatrixEmbedding B D,
    ∃ eC : BananaMatrixEmbedding C D,
      (∀ x, eB.left (f.left x) = eC.left (g.left x)) ∧
      (∀ y, eB.right (f.right y) = eC.right (g.right y)) ∧
      (∀ x y, eB.left x = eC.left y ↔
        ∃ z, x = f.left z ∧ y = g.left z) ∧
      (∀ x y, eB.right x = eC.right y ↔
        ∃ z, x = f.right z ∧ y = g.right z) := by
  obtain ⟨pBL, pBR, hpBL, hpBR⟩ := f.exists_sort_retractions
  obtain ⟨pCL, pCR, hpCL, hpCR⟩ := g.exists_sort_retractions
  refine ⟨bananaTripleAmalgam A B C f g,
    bananaTripleAmalgamInl A B C f g pBL pBR,
    bananaTripleAmalgamInr A B C f g pCL pCR, ?_, ?_, ?_, ?_⟩
  · intro x
    exact tripleInl_comp_eq_tripleInr_comp
      f.left g.left pBL pCL hpBL hpCL x
  · intro y
    exact tripleInl_comp_eq_tripleInr_comp
      f.right g.right pBR pCR hpBR hpCR y
  · intro x y
    exact tripleInl_eq_tripleInr_iff_common
      f.left g.left pBL pCL hpBL hpCL x y
  · intro x y
    exact tripleInl_eq_tripleInr_iff_common
      f.right g.right pBR pCR hpBR hpCR x y

end SuccessorTree.NonPrecompact
