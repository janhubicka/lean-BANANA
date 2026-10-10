import BANANA.NonPrecompact.BananaPerfectSplitSystemEmbeddings

/-!
# Strong intersection of split perfect BANANA systems

For the canonical embeddings B=A⊥B₀ and C=A⊥C₀ into the
triple perfect pair D=A⊥B₀⊥C₀, the intersection of the
images is exactly the shared first A block, on each sort.

This is stronger than the amalgamation property needed for the
cofinal perfect-total systems in the ample-generics argument.
It also ensures the canonical common embeddings are not
silently identifying elements of the two complements.
-/

namespace SuccessorTree.NonPrecompact

/-- Equality of the images of two split-system vectors forces both
complement coordinates to vanish and their shared coordinates to agree. -/
theorem bananaPerfectSplit_overlap
    (a b c : ℕ)
    (x : Fin (a + b) → F2)
    (y : Fin (a + c) → F2) :
    bananaPerfectSplitEmbedB a b c x =
      bananaPerfectSplitEmbedC a b c y ↔
      ∃ z : Fin a → F2,
        x = Fin.append z (0 : Fin b → F2) ∧
        y = Fin.append z (0 : Fin c → F2) := by
  constructor
  · intro h
    have hA :
        BananaMatrixStructure.finLeftPart x =
          BananaMatrixStructure.finLeftPart y := by
      have hh := congrArg
        (fun v : Fin (a + (b + c)) → F2 =>
          BananaMatrixStructure.finLeftPart v) h
      simpa [bananaPerfectSplitEmbedB,
        bananaPerfectSplitEmbedC] using hh
    have hBC :
        Fin.append (BananaMatrixStructure.finRightPart x)
          (0 : Fin c → F2) =
        Fin.append (0 : Fin b → F2)
          (BananaMatrixStructure.finRightPart y) := by
      have hh := congrArg
        (fun v : Fin (a + (b + c)) → F2 =>
          (BananaMatrixStructure.finRightPart v :
            Fin (b + c) → F2)) h
      simpa [bananaPerfectSplitEmbedB,
        bananaPerfectSplitEmbedC] using hh
    have hB :
        BananaMatrixStructure.finRightPart x = 0 := by
      have hh := congrArg
        (fun v : Fin (b + c) → F2 =>
          BananaMatrixStructure.finLeftPart v) hBC
      simpa using hh
    have hC :
        BananaMatrixStructure.finRightPart y = 0 := by
      have hh := congrArg
        (fun v : Fin (b + c) → F2 =>
          BananaMatrixStructure.finRightPart v) hBC
      simpa using hh.symm
    refine ⟨BananaMatrixStructure.finLeftPart x, ?_, ?_⟩
    · calc
        x = Fin.append (BananaMatrixStructure.finLeftPart x)
            (BananaMatrixStructure.finRightPart x) :=
          (bananaPerfectSplit_append_parts x).symm
        _ = Fin.append (BananaMatrixStructure.finLeftPart x)
            (0 : Fin b → F2) := by rw [hB]
    · calc
        y = Fin.append (BananaMatrixStructure.finLeftPart y)
            (BananaMatrixStructure.finRightPart y) :=
          (bananaPerfectSplit_append_parts y).symm
        _ = Fin.append (BananaMatrixStructure.finLeftPart x)
            (0 : Fin c → F2) := by rw [← hA, hC]
  · rintro ⟨z, rfl, rfl⟩
    simp [bananaPerfectSplitEmbedB, bananaPerfectSplitEmbedC]

/-- Strong intersection for the genuine BANANA left embeddings. -/
theorem bananaPerfectSplitEmbedding_strong_left
    (a b c : ℕ)
    (x : Fin (a + b) → F2)
    (y : Fin (a + c) → F2) :
    (bananaPerfectSplitEmbeddingB a b c).left x =
      (bananaPerfectSplitEmbeddingC a b c).left y ↔
      ∃ z : Fin a → F2,
        x = Fin.append z (0 : Fin b → F2) ∧
        y = Fin.append z (0 : Fin c → F2) :=
  bananaPerfectSplit_overlap a b c x y

/-- Strong intersection for the genuine BANANA right embeddings. -/
theorem bananaPerfectSplitEmbedding_strong_right
    (a b c : ℕ)
    (x : Fin (a + b) → F2)
    (y : Fin (a + c) → F2) :
    (bananaPerfectSplitEmbeddingB a b c).right x =
      (bananaPerfectSplitEmbeddingC a b c).right y ↔
      ∃ z : Fin a → F2,
        x = Fin.append z (0 : Fin b → F2) ∧
        y = Fin.append z (0 : Fin c → F2) :=
  bananaPerfectSplit_overlap a b c x y

end SuccessorTree.NonPrecompact
