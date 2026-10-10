import BANANA.NonPrecompact.BananaPerfectTripleAutomorphisms

/-!
# Matching two split perfect-total systems inside a triple pairing

The perfect systems B=A⊥B₀ and C=A⊥C₀ embed
in D=A⊥B₀⊥C₀ by identifying A and using distinct complementary
blocks. An automorphism of D assembled from fA, fB, fC
intertwines both automorphisms of B and C, on both sorts.
This is the standard-coordinate compatibility calculation in the
amalgamation argument for ample generics.

The embeddings are given as coordinate functions here. Their
linearity, injectivity and induced pairing preservation are
separate formalisation steps.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- The canonical coordinate inclusion of A⊥B₀ into A⊥B₀⊥C₀. -/
def bananaPerfectSplitEmbedB (a b c : ℕ)
    (x : Fin (a + b) → F2) : Fin (a + (b + c)) → F2 :=
  Fin.append (BananaMatrixStructure.finLeftPart x)
    (Fin.append (BananaMatrixStructure.finRightPart x)
      (0 : Fin c → F2))

/-- The canonical coordinate inclusion of A⊥C₀ into A⊥B₀⊥C₀. -/
def bananaPerfectSplitEmbedC (a b c : ℕ)
    (x : Fin (a + c) → F2) : Fin (a + (b + c)) → F2 :=
  Fin.append (BananaMatrixStructure.finLeftPart x)
    (Fin.append (0 : Fin b → F2)
      (BananaMatrixStructure.finRightPart x))

/-- The triple left action intertwines the left B-system action. -/
theorem bananaPerfectTriple_intertwines_left_B
    {a b c : ℕ}
    (fA : FinitePerfectGL a)
    (fB : FinitePerfectGL b)
    (fC : FinitePerfectGL c)
    (x : Fin (a + b) → F2) :
    (bananaPerfectTripleAutomorphism fA fB fC).left
      (bananaPerfectSplitEmbedB a b c x) =
    bananaPerfectSplitEmbedB a b c
      (BananaMatrixStructure.directSumLinearEquiv fA fB x) := by
  change bananaPerfectTripleLeft fA fB fC
      (bananaPerfectSplitEmbedB a b c x) = _
  simp [bananaPerfectTripleLeft, bananaPerfectSplitEmbedB,
    BananaMatrixStructure.directSumLinearEquiv_apply]

/-- The triple left action also intertwines the C-system action. -/
theorem bananaPerfectTriple_intertwines_left_C
    {a b c : ℕ}
    (fA : FinitePerfectGL a)
    (fB : FinitePerfectGL b)
    (fC : FinitePerfectGL c)
    (x : Fin (a + c) → F2) :
    (bananaPerfectTripleAutomorphism fA fB fC).left
      (bananaPerfectSplitEmbedC a b c x) =
    bananaPerfectSplitEmbedC a b c
      (BananaMatrixStructure.directSumLinearEquiv fA fC x) := by
  change bananaPerfectTripleLeft fA fB fC
      (bananaPerfectSplitEmbedC a b c x) = _
  simp [bananaPerfectTripleLeft, bananaPerfectSplitEmbedC,
    BananaMatrixStructure.directSumLinearEquiv_apply]

/-- The triple contragredient intertwines the right B-system action. -/
theorem bananaPerfectTriple_intertwines_right_B
    {a b c : ℕ}
    (fA : FinitePerfectGL a)
    (fB : FinitePerfectGL b)
    (fC : FinitePerfectGL c)
    (x : Fin (a + b) → F2) :
    (bananaPerfectTripleAutomorphism fA fB fC).right
      (bananaPerfectSplitEmbedB a b c x) =
    bananaPerfectSplitEmbedB a b c
      (BananaMatrixStructure.directSumLinearEquiv
        (dotContragredient fA) (dotContragredient fB) x) := by
  change dotContragredient (bananaPerfectTripleLeft fA fB fC)
      (bananaPerfectSplitEmbedB a b c x) = _
  rw [bananaPerfectTripleLeft,
    BananaMatrixStructure.dotContragredient_directSumLinearEquiv,
    BananaMatrixStructure.dotContragredient_directSumLinearEquiv]
  simp [bananaPerfectSplitEmbedB,
    BananaMatrixStructure.directSumLinearEquiv_apply]

/-- The triple contragredient intertwines the right C-system action. -/
theorem bananaPerfectTriple_intertwines_right_C
    {a b c : ℕ}
    (fA : FinitePerfectGL a)
    (fB : FinitePerfectGL b)
    (fC : FinitePerfectGL c)
    (x : Fin (a + c) → F2) :
    (bananaPerfectTripleAutomorphism fA fB fC).right
      (bananaPerfectSplitEmbedC a b c x) =
    bananaPerfectSplitEmbedC a b c
      (BananaMatrixStructure.directSumLinearEquiv
        (dotContragredient fA) (dotContragredient fC) x) := by
  change dotContragredient (bananaPerfectTripleLeft fA fB fC)
      (bananaPerfectSplitEmbedC a b c x) = _
  rw [bananaPerfectTripleLeft,
    BananaMatrixStructure.dotContragredient_directSumLinearEquiv,
    BananaMatrixStructure.dotContragredient_directSumLinearEquiv]
  simp [bananaPerfectSplitEmbedC,
    BananaMatrixStructure.directSumLinearEquiv_apply]

end SuccessorTree.NonPrecompact
