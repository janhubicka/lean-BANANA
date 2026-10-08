import BANANA.NonPrecompact.LinePairEmbeddingDegree
import BANANA.NonPrecompact.PerfectHomogeneity
import BANANA.NonPrecompact.PerfectLeftRange

/-!
# Extension of prescribed four-element BANANA substructures

The perfect-pair homogeneity lemma upgrades the embedding of a small
two-sorted source into an arbitrary BANANA structure to a useful
extension property. Once an arbitrary source A has been completed into
a sufficiently large perfect pairing, every embedding of a chosen
four-element substructure into the perfect target extends to an
embedding of A. This is the finite geometric ingredient needed for
instantiating copy Ramsey-degree propagation in the BANANA class.
-/

namespace SuccessorTree.NonPrecompact

/-- Every prescribed image of a four-element substructure extends to
an embedding of the full finite source into a large enough perfect
pairing. The extra dimension may be zero. -/
theorem BananaMatrixStructure.exists_linePairExtension_in_perfectBlock
    {l r : ℕ} (A : BananaMatrixStructure l r)
    {b : F2}
    (i : BananaMatrixEmbedding (linePairSource b) A)
    (extra : ℕ)
    (e : BananaMatrixEmbedding
      (linePairSource b) (perfectBanana ((l + r) + extra))) :
    ∃ F : BananaMatrixEmbedding A (perfectBanana ((l + r) + extra)),
      (∀ x : Fin 1 → F2, F.left (i.left x) = e.left x) ∧
      (∀ y : Fin 1 → F2, F.right (i.right y) = e.right y) := by
  let j : BananaMatrixEmbedding
      (perfectBanana (l + r))
      (perfectBanana ((l + r) + extra)) :=
    BananaMatrixStructure.standardPerfectBlockEmbedding (l + r) extra
  let base : BananaMatrixEmbedding A
      (perfectBanana ((l + r) + extra)) :=
    BananaMatrixEmbedding.comp j A.completionEmbedding
  let old : BananaMatrixEmbedding
      (linePairSource b) (perfectBanana ((l + r) + extra)) :=
    BananaMatrixEmbedding.comp base i
  obtain ⟨H, hleft, hright⟩ :=
    exists_perfectPairAutomorphism_extends old e
  let F : BananaMatrixEmbedding A
      (perfectBanana ((l + r) + extra)) :=
    BananaMatrixEmbedding.comp H base
  refine ⟨F, ?_, ?_⟩
  · intro x
    exact hleft x
  · intro y
    exact hright y

/-- Vector-pair version of the same extension result: every copy of
the four-element source inside the perfect block is the restriction
of an embedding of A, along a prescribed source substructure. -/
theorem BananaMatrixStructure.exists_extend_linePairCopy
    {l r : ℕ} (A : BananaMatrixStructure l r)
    {b : F2}
    (i : BananaMatrixEmbedding (linePairSource b) A)
    (extra : ℕ)
    (P : BananaLinePairCopy
      (perfectBanana ((l + r) + extra)) b) :
    ∃ F : BananaMatrixEmbedding A
        (perfectBanana ((l + r) + extra)),
      (BananaMatrixEmbedding.comp F i).toLinePairCopy = P := by
  obtain ⟨F, hleft, hright⟩ :=
    A.exists_linePairExtension_in_perfectBlock i extra
      P.toSourceEmbedding
  refine ⟨F, ?_⟩
  apply BananaLinePairCopy.eq_of_vectors
  · simpa only [BananaLinePairCopy.toSourceEmbedding_left_basis] using
      hleft (Pi.single (0 : Fin 1) 1)
  · simpa only [BananaLinePairCopy.toSourceEmbedding_right_basis] using
      hright (Pi.single (0 : Fin 1) 1)

end SuccessorTree.NonPrecompact
