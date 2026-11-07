import BANANA.NonPrecompact.BananaMatrixEmbeddedCompletionHom
import BANANA.NonPrecompact.BananaMatrixRepresentativeIso
import BANANA.NonPrecompact.PerfectBlockConjugator

/-!
# Uniform aligned actions and ambient conjugators

The original coherent-EPPA witness is a perfect pairing of side dimension n.
An embedded representative of dimensions l and r can be completed inside the
same witness whenever l+r ≤ n. The same homomorphism then extends all
automorphisms of the representative. For every isomorphic embedded copy,
finite perfect-pair homogeneity supplies one ambient automorphism which
identifies the chosen representative with that copy on both sorts.

This removes two existential hypotheses from the typed transport API.
It does not yet construct representatives for every substructure of A.
-/

namespace SuccessorTree.NonPrecompact

/-- The dimension bound supplies a standard perfect-block embedding
required by the already packaged aligned-completion homomorphism. -/
theorem exists_bananaMatrixAlignedCompletionHom_of_le
    {l r n : ℕ} (A : BananaMatrixStructure l r)
    (j₀ : BananaMatrixEmbedding A (perfectBanana n))
    (h : l + r ≤ n) :
    ∃ rho : BananaMatrixAutGroup A →*
        BananaMatrixAutGroup (perfectBanana n),
      ∀ f : BananaMatrixAutGroup A,
        (∀ x, (rho f).1.1 (j₀.left x) = j₀.left (f.1.1 x)) ∧
        (∀ y, (rho f).1.2 (j₀.right y) = j₀.right (f.1.2 y)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = (l + r) + k := by
    refine ⟨n - (l + r), ?_⟩
    omega
  subst n
  exact exists_bananaMatrixAlignedCompletionHom A j₀
    (BananaMatrixStructure.standardPerfectBlockEmbedding (l + r) k)

/-- One ambient conjugator identifies two embedded copies on both sorts.
No nondegeneracy assumption is made on the representative. -/
theorem exists_bananaMatrixRepresentativeConjugator
    {l r l' r' n : ℕ}
    {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure l' r'}
    (j₀ : BananaMatrixEmbedding A (perfectBanana n))
    (j : BananaMatrixEmbedding B (perfectBanana n))
    (i : BananaMatrixIso A B) :
    ∃ g : BananaMatrixAutGroup (perfectBanana n),
      (∀ x, g.1.1 (j₀.left x) = j.left (i.left x)) ∧
      (∀ y, g.1.2 (j₀.right y) = j.right (i.right y)) := by
  let e : BananaMatrixEmbedding A (perfectBanana n) :=
    BananaMatrixEmbedding.comp j i.toEmbedding
  obtain ⟨H, hL, hR⟩ :=
    exists_perfectPairAutomorphism_extends j₀ e
  refine ⟨H.toAutGroup, ?_, ?_⟩
  · intro x
    exact (H.toAutGroup_left_apply x).trans (hL x)
  · intro y
    exact (H.toAutGroup_right_apply y).trans (hR y)

end SuccessorTree.NonPrecompact
