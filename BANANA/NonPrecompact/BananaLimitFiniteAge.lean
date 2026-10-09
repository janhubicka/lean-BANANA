import BANANA.NonPrecompact.BananaLimitBlockCofinality
import BANANA.NonPrecompact.BananaFiniteFraisseProperties

/-!
# Finite substructures of the explicit BANANA limit

Every finite two-sorted subspace of the rational finite-support limit
is isomorphic to a finite standard-coordinate BANANA pairing.
First cover both sorts by one finite perfect coordinate block,
then use the already-verified hereditary property of finite pairings
to realise the two selected subspaces inside that block.

Combined with the previously kernel-verified universality theorem
`BananaMatrixStructure.embeds_in_explicit_limit`, this is the
concrete finite-structure content of `Age(M)=K`.

This module does not claim global ultrahomogeneity, or the
model-theoretic identification of the abstract Fraïssé limit.
-/

namespace SuccessorTree.NonPrecompact

/-- Composition of a finite BANANA embedding with an embedding
of its ambient finite structure into the explicit countable model. -/
noncomputable def BananaMatrixEmbeddingToLimit.comp
    {aL aR bL bR : ℕ}
    {A : BananaMatrixStructure aL aR}
    {B : BananaMatrixStructure bL bR}
    (E : BananaMatrixEmbeddingToLimit B)
    (f : BananaMatrixEmbedding A B) :
    BananaMatrixEmbeddingToLimit A where
  left := E.left.comp f.left
  right := E.right.comp f.right
  left_injective := E.left_injective.comp f.left_injective
  right_injective := E.right_injective.comp f.right_injective
  pairing_apply := by
    intro x y
    exact (E.pairing_apply (f.left x) (f.right y)).trans
      (f.pairing_apply x y)

/-- Every pair of finite subspaces of the explicit countable pairing
is the *exact* two-sort range of an embedded finite BANANA structure.
There is no choice of a shared basis between the two sorts. -/
theorem exists_finite_banana_substructure_of_limit
    (U V : Submodule F2 BananaLimitVector)
    [Finite U] [Finite V] :
    ∃ l r : ℕ,
    ∃ A : BananaMatrixStructure l r,
    ∃ e : BananaMatrixEmbeddingToLimit A,
      LinearMap.range e.left = U ∧
      LinearMap.range e.right = V := by
  classical
  obtain ⟨n, E, hU, hV⟩ :=
    exists_perfect_block_containing_finite_subspaces U V
  let U0 : Submodule F2 (Fin n → F2) := U.comap E.left
  let V0 : Submodule F2 (Fin n → F2) := V.comap E.right
  obtain ⟨l, r, A, f, hfL, hfR⟩ :=
    (perfectBanana n).exists_substructure_with_ranges U0 V0
  let e : BananaMatrixEmbeddingToLimit A := E.comp f
  refine ⟨l, r, A, e, ?_, ?_⟩
  · apply Submodule.ext
    intro z
    constructor
    · rintro ⟨x, rfl⟩
      have hx : f.left x ∈ U0 := by
        rw [← hfL]
        exact ⟨x, rfl⟩
      exact hx
    · intro hz
      obtain ⟨x, hx⟩ := hU ⟨z, hz⟩
      have hxU : x ∈ U0 := by
        change E.left x ∈ U
        simpa only [hx] using hz
      have hxRange : x ∈ LinearMap.range f.left := by
        rw [hfL]
        exact hxU
      obtain ⟨a, ha⟩ := hxRange
      refine ⟨a, ?_⟩
      change E.left (f.left a) = z
      rw [ha]
      exact hx
  · apply Submodule.ext
    intro z
    constructor
    · rintro ⟨y, rfl⟩
      have hy : f.right y ∈ V0 := by
        rw [← hfR]
        exact ⟨y, rfl⟩
      exact hy
    · intro hz
      obtain ⟨y, hy⟩ := hV ⟨z, hz⟩
      have hyV : y ∈ V0 := by
        change E.right y ∈ V
        simpa only [hy] using hz
      have hyRange : y ∈ LinearMap.range f.right := by
        rw [hfR]
        exact hyV
      obtain ⟨a, ha⟩ := hyRange
      refine ⟨a, ?_⟩
      change E.right (f.right a) = z
      rw [ha]
      exact hy

/-- Finite substructure representation and universality together:
every finite BANANA matrix system occurs in the explicit limit,
and every finite two-sorted subspace of that limit has finite matrix
coordinates and its inherited pairing. -/
theorem banana_limit_finite_age_two_directions :
    (∀ l r : ℕ, ∀ A : BananaMatrixStructure l r,
      Nonempty (BananaMatrixEmbeddingToLimit A)) ∧
    (∀ (U V : Submodule F2 BananaLimitVector),
      Finite U → Finite V →
      ∃ l r : ℕ, ∃ A : BananaMatrixStructure l r,
      ∃ e : BananaMatrixEmbeddingToLimit A,
        LinearMap.range e.left = U ∧
        LinearMap.range e.right = V) := by
  constructor
  · intro l r A
    exact A.embeds_in_explicit_limit
  · intro U V hU hV
    letI : Finite U := hU
    letI : Finite V := hV
    exact exists_finite_banana_substructure_of_limit U V

end SuccessorTree.NonPrecompact
