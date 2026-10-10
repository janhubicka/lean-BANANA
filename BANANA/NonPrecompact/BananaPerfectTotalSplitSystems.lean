import BANANA.NonPrecompact.BananaPerfectSplitSystemEmbeddings
import BANANA.NonPrecompact.BananaPerfectSplitSystemActions

/-!
# Simultaneous amalgamation of split perfect total n-systems

Fix n many compatible automorphisms of the shared perfect block A
and arbitrary automorphisms of the disjoint perfect blocks B₀, C₀.
The associated n automorphisms of B=A⊥B₀ and C=A⊥C₀
are simultaneously intertwined by n automorphisms of
D=A⊥B₀⊥C₀ under the genuine embeddings of both systems.

The same underlying embeddings are used for all n named maps.
This is the finite standard-coordinate version of amalgamation of
perfect total n-systems, not yet the reduction of arbitrary perfect
embedded systems to split coordinates.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- The prescribed automorphism of the first split perfect system. -/
noncomputable def bananaPerfectTotalSplitActionB
    {a b : ℕ} (fA : FinitePerfectGL a) (fB : FinitePerfectGL b) :
    BananaMatrixEmbedding
      (perfectBanana (a + b)) (perfectBanana (a + b)) :=
  perfectPairAutomorphismOfLinearEquiv
    (BananaMatrixStructure.directSumLinearEquiv fA fB)

/-- The prescribed automorphism of the second split perfect system. -/
noncomputable def bananaPerfectTotalSplitActionC
    {a c : ℕ} (fA : FinitePerfectGL a) (fC : FinitePerfectGL c) :
    BananaMatrixEmbedding
      (perfectBanana (a + c)) (perfectBanana (a + c)) :=
  perfectPairAutomorphismOfLinearEquiv
    (BananaMatrixStructure.directSumLinearEquiv fA fC)

/-- One perfect triple-block system simultaneously amalgamates the
two compatible perfect total systems, with the two fixed embeddings
working for *every* named automorphism on both sorts. -/
theorem exists_bananaPerfectTotalSplitSystem_amalgam
    {n a b c : ℕ}
    (fA : Fin n → FinitePerfectGL a)
    (fB : Fin n → FinitePerfectGL b)
    (fC : Fin n → FinitePerfectGL c) :
    ∃ F : Fin n →
      BananaMatrixEmbedding
        (perfectBanana (a + (b + c)))
        (perfectBanana (a + (b + c))),
      (∀ i x,
        (F i).left ((bananaPerfectSplitEmbeddingB a b c).left x) =
          (bananaPerfectSplitEmbeddingB a b c).left
            ((bananaPerfectTotalSplitActionB (fA i) (fB i)).left x)) ∧
      (∀ i y,
        (F i).right ((bananaPerfectSplitEmbeddingB a b c).right y) =
          (bananaPerfectSplitEmbeddingB a b c).right
            ((bananaPerfectTotalSplitActionB (fA i) (fB i)).right y)) ∧
      (∀ i x,
        (F i).left ((bananaPerfectSplitEmbeddingC a b c).left x) =
          (bananaPerfectSplitEmbeddingC a b c).left
            ((bananaPerfectTotalSplitActionC (fA i) (fC i)).left x)) ∧
      (∀ i y,
        (F i).right ((bananaPerfectSplitEmbeddingC a b c).right y) =
          (bananaPerfectSplitEmbeddingC a b c).right
            ((bananaPerfectTotalSplitActionC (fA i) (fC i)).right y)) := by
  refine ⟨fun i => bananaPerfectTripleAutomorphism
    (fA i) (fB i) (fC i), ?_, ?_, ?_, ?_⟩
  · intro i x
    exact bananaPerfectTriple_intertwines_left_B (fA i) (fB i) (fC i) x
  · intro i y
    change (bananaPerfectTripleAutomorphism
        (fA i) (fB i) (fC i)).right
        (bananaPerfectSplitEmbedB a b c y) =
      bananaPerfectSplitEmbedB a b c
        (dotContragredient
          (BananaMatrixStructure.directSumLinearEquiv
            (fA i) (fB i)) y)
    rw [BananaMatrixStructure.dotContragredient_directSumLinearEquiv]
    exact bananaPerfectTriple_intertwines_right_B
      (fA i) (fB i) (fC i) y
  · intro i x
    exact bananaPerfectTriple_intertwines_left_C (fA i) (fB i) (fC i) x
  · intro i y
    change (bananaPerfectTripleAutomorphism
        (fA i) (fB i) (fC i)).right
        (bananaPerfectSplitEmbedC a b c y) =
      bananaPerfectSplitEmbedC a b c
        (dotContragredient
          (BananaMatrixStructure.directSumLinearEquiv
            (fA i) (fC i)) y)
    rw [BananaMatrixStructure.dotContragredient_directSumLinearEquiv]
    exact bananaPerfectTriple_intertwines_right_C
      (fA i) (fB i) (fC i) y

end SuccessorTree.NonPrecompact
