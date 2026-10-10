import BANANA.NonPrecompact.BananaStructure

/-!
# Finite systems of partial automorphisms of BANANA structures

An n-system consists of a finite matrix pairing A and n pairs of embeddings
of a common source Dᵢ into A. The two images describe the domain and range
of the corresponding partial automorphism; Dᵢ and Dⱼ may have different
dimensions, and zero-dimensional sorts are allowed.

An embedding of n-systems is not merely an embedding of their carriers:
for every named partial map the induced maps on its source have to make
both the domain and range squares commute. Recording this explicitly
avoids losing compatibility when formulating JEP and WAP.

This file establishes identities, composition, and uniqueness of the
induced source maps. It does not assert amalgamation or WAP.
-/

namespace SuccessorTree.NonPrecompact

/-- Identity embedding of a finite BANANA matrix pairing. -/
def BananaMatrixEmbedding.id
    {l r : ℕ} (A : BananaMatrixStructure l r) :
    BananaMatrixEmbedding A A where
  left := LinearMap.id
  right := LinearMap.id
  left_injective := by
    intro x y h
    simpa using h
  right_injective := by
    intro x y h
    simpa using h
  pairing_apply := by
    intro x y
    rfl

/-- A finite system of n labelled partial automorphisms.
Each partial automorphism is represented by its domain and range
embeddings of one and the same finite source structure. -/
structure BananaFinitePartialSystem (n : ℕ) where
  leftDim : ℕ
  rightDim : ℕ
  carrier : BananaMatrixStructure leftDim rightDim
  sourceLeftDim : Fin n → ℕ
  sourceRightDim : Fin n → ℕ
  source : ∀ i : Fin n,
    BananaMatrixStructure (sourceLeftDim i) (sourceRightDim i)
  domain : ∀ i : Fin n, BananaMatrixEmbedding (source i) carrier
  range : ∀ i : Fin n, BananaMatrixEmbedding (source i) carrier

/-- A morphism of n-systems: a carrier embedding and compatible
embeddings of every named partial-isomorphism source. Compatibility
is required on both vector-space sorts and at both ends of each
partial map. -/
structure BananaFinitePartialSystemEmbedding {n : ℕ}
    (S T : BananaFinitePartialSystem n) where
  carrier : BananaMatrixEmbedding S.carrier T.carrier
  source : ∀ i : Fin n, BananaMatrixEmbedding (S.source i) (T.source i)
  domain_left : ∀ i (x : Fin (S.sourceLeftDim i) → F2),
    carrier.left ((S.domain i).left x) =
      (T.domain i).left ((source i).left x)
  domain_right : ∀ i (y : Fin (S.sourceRightDim i) → F2),
    carrier.right ((S.domain i).right y) =
      (T.domain i).right ((source i).right y)
  range_left : ∀ i (x : Fin (S.sourceLeftDim i) → F2),
    carrier.left ((S.range i).left x) =
      (T.range i).left ((source i).left x)
  range_right : ∀ i (y : Fin (S.sourceRightDim i) → F2),
    carrier.right ((S.range i).right y) =
      (T.range i).right ((source i).right y)

namespace BananaFinitePartialSystemEmbedding

variable {n : ℕ}

/-- Every n-system has an identity morphism. -/
def id (S : BananaFinitePartialSystem n) :
    BananaFinitePartialSystemEmbedding S S where
  carrier := BananaMatrixEmbedding.id S.carrier
  source := fun i => BananaMatrixEmbedding.id (S.source i)
  domain_left := by
    intro i x
    rfl
  domain_right := by
    intro i y
    rfl
  range_left := by
    intro i x
    rfl
  range_right := by
    intro i y
    rfl

/-- Composition preserves all four commuting squares for every
named partial automorphism. -/
def comp
    {S T U : BananaFinitePartialSystem n}
    (g : BananaFinitePartialSystemEmbedding T U)
    (f : BananaFinitePartialSystemEmbedding S T) :
    BananaFinitePartialSystemEmbedding S U where
  carrier := BananaMatrixEmbedding.comp g.carrier f.carrier
  source := fun i =>
    BananaMatrixEmbedding.comp (g.source i) (f.source i)
  domain_left := by
    intro i x
    change g.carrier.left
        (f.carrier.left ((S.domain i).left x)) =
      (U.domain i).left
        ((g.source i).left ((f.source i).left x))
    rw [f.domain_left i x, g.domain_left i ((f.source i).left x)]
  domain_right := by
    intro i y
    change g.carrier.right
        (f.carrier.right ((S.domain i).right y)) =
      (U.domain i).right
        ((g.source i).right ((f.source i).right y))
    rw [f.domain_right i y, g.domain_right i ((f.source i).right y)]
  range_left := by
    intro i x
    change g.carrier.left
        (f.carrier.left ((S.range i).left x)) =
      (U.range i).left
        ((g.source i).left ((f.source i).left x))
    rw [f.range_left i x, g.range_left i ((f.source i).left x)]
  range_right := by
    intro i y
    change g.carrier.right
        (f.carrier.right ((S.range i).right y)) =
      (U.range i).right
        ((g.source i).right ((f.source i).right y))
    rw [f.range_right i y, g.range_right i ((f.source i).right y)]

/-- The source map on the left sort is uniquely forced by the
carrier map and commutativity of the domain square. -/
theorem source_left_unique
    {S T : BananaFinitePartialSystem n}
    (f : BananaFinitePartialSystemEmbedding S T)
    (i : Fin n) (x : Fin (S.sourceLeftDim i) → F2)
    (z : Fin (T.sourceLeftDim i) → F2)
    (hz : (T.domain i).left z =
      f.carrier.left ((S.domain i).left x)) :
    z = (f.source i).left x := by
  apply (T.domain i).left_injective
  exact hz.trans (f.domain_left i x)

/-- The source map on the right sort is uniquely forced by the
carrier map and commutativity of the domain square. -/
theorem source_right_unique
    {S T : BananaFinitePartialSystem n}
    (f : BananaFinitePartialSystemEmbedding S T)
    (i : Fin n) (y : Fin (S.sourceRightDim i) → F2)
    (z : Fin (T.sourceRightDim i) → F2)
    (hz : (T.domain i).right z =
      f.carrier.right ((S.domain i).right y)) :
    z = (f.source i).right y := by
  apply (T.domain i).right_injective
  exact hz.trans (f.domain_right i y)

end BananaFinitePartialSystemEmbedding

end SuccessorTree.NonPrecompact
