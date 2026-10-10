import BANANA.NonPrecompact.BananaPerfectTotalEquivariantDiagram
import BANANA.NonPrecompact.BananaTotalFamilyPerfectCompletion

/-!
# Perfect-total amalgamation of finite BANANA n-system diagrams

Every diagram A ↪ B,C of finite standard perfect pairings, with
compatible Fin n-indexed total automorphisms, has a common *perfect*
finite pairing D' and compatible total automorphisms extending both
systems.

The first step is the canonical equivariant redundant amalgam D,
which need not be perfect. The second step embeds D into its
canonical perfect completion D' and simultaneously extends every
named automorphism. Both embeddings B,C ↪ D' are genuine BANANA
embeddings, agree pointwise on A, and intertwine all n actions
on both sorts.

This is the algebraic amalgamation theorem. The passage to the
categorical class of n-systems and its JEP/WAP consequences are
handled separately.
-/

namespace SuccessorTree.NonPrecompact

/-- Arbitrary compatible diagrams of finite perfect-total BANANA
pairings have a common finite *perfect-total* amalgam, with a
single pair of embeddings intertwining every named automorphism. -/
theorem exists_bananaPerfectTotalSystem_perfect_amalgam
    {n a b c : ℕ}
    (f : BananaMatrixEmbedding (perfectBanana a) (perfectBanana b))
    (g : BananaMatrixEmbedding (perfectBanana a) (perfectBanana c))
    (FA : Fin n → BananaMatrixEmbedding
      (perfectBanana a) (perfectBanana a))
    (FB : Fin n → BananaMatrixEmbedding
      (perfectBanana b) (perfectBanana b))
    (FC : Fin n → BananaMatrixEmbedding
      (perfectBanana c) (perfectBanana c))
    (hBL : ∀ i x, (FB i).left (f.left x) = f.left ((FA i).left x))
    (hBR : ∀ i y, (FB i).right (f.right y) = f.right ((FA i).right y))
    (hCL : ∀ i x, (FC i).left (g.left x) = g.left ((FA i).left x))
    (hCR : ∀ i y, (FC i).right (g.right y) = g.right ((FA i).right y)) :
    ∃ k : ℕ,
    ∃ eB : BananaMatrixEmbedding (perfectBanana b) (perfectBanana k),
    ∃ eC : BananaMatrixEmbedding (perfectBanana c) (perfectBanana k),
    ∃ FK : Fin n → BananaMatrixEmbedding
      (perfectBanana k) (perfectBanana k),
      (∀ x, eB.left (f.left x) = eC.left (g.left x)) ∧
      (∀ y, eB.right (f.right y) = eC.right (g.right y)) ∧
      (∀ i x, (FK i).left (eB.left x) = eB.left ((FB i).left x)) ∧
      (∀ i y, (FK i).right (eB.right y) = eB.right ((FB i).right y)) ∧
      (∀ i x, (FK i).left (eC.left x) = eC.left ((FC i).left x)) ∧
      (∀ i y, (FK i).right (eC.right y) = eC.right ((FC i).right y)) := by
  obtain ⟨D, eB, eC, HD, hAL, hAR, hBL', hBR', hCL', hCR'⟩ :=
    exists_bananaPerfectTotalSystem_redundant_amalgam
      f g FA FB FC hBL hBR hCL hCR
  obtain ⟨FK, hKL, hKR⟩ :=
    exists_bananaTotalFamily_commonPerfectCompletion D HD
  let k := (((a + b) + c) + ((a + b) + c))
  let j : BananaMatrixEmbedding D (perfectBanana k) :=
    D.completionEmbedding
  let fB : BananaMatrixEmbedding (perfectBanana b) (perfectBanana k) :=
    BananaMatrixEmbedding.comp j eB
  let fC : BananaMatrixEmbedding (perfectBanana c) (perfectBanana k) :=
    BananaMatrixEmbedding.comp j eC
  refine ⟨k, fB, fC, FK, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    change j.left (eB.left (f.left x)) =
      j.left (eC.left (g.left x))
    rw [hAL x]
  · intro y
    change j.right (eB.right (f.right y)) =
      j.right (eC.right (g.right y))
    rw [hAR y]
  · intro i x
    change (FK i).left (j.left (eB.left x)) =
      j.left (eB.left ((FB i).left x))
    calc
      (FK i).left (j.left (eB.left x)) =
          j.left ((HD i).left (eB.left x)) := hKL i (eB.left x)
      _ = j.left (eB.left ((FB i).left x)) := by rw [hBL' i x]
  · intro i y
    change (FK i).right (j.right (eB.right y)) =
      j.right (eB.right ((FB i).right y))
    calc
      (FK i).right (j.right (eB.right y)) =
          j.right ((HD i).right (eB.right y)) := hKR i (eB.right y)
      _ = j.right (eB.right ((FB i).right y)) := by rw [hBR' i y]
  · intro i x
    change (FK i).left (j.left (eC.left x)) =
      j.left (eC.left ((FC i).left x))
    calc
      (FK i).left (j.left (eC.left x)) =
          j.left ((HD i).left (eC.left x)) := hKL i (eC.left x)
      _ = j.left (eC.left ((FC i).left x)) := by rw [hCL' i x]
  · intro i y
    change (FK i).right (j.right (eC.right y)) =
      j.right (eC.right ((FC i).right y))
    calc
      (FK i).right (j.right (eC.right y)) =
          j.right ((HD i).right (eC.right y)) := hKR i (eC.right y)
      _ = j.right (eC.right ((FC i).right y)) := by rw [hCR' i y]

end SuccessorTree.NonPrecompact
