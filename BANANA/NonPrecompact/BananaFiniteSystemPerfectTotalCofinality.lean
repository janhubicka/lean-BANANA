import BANANA.NonPrecompact.BananaFinitePartialSystems
import BANANA.NonPrecompact.PerfectCofinalTotalSystems
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Cofinality of perfect total objects in the category of BANANA n-systems

The common-completion theorem supplies one finite perfect pairing and
one ambient automorphism for each of the n partial isomorphisms.
Here we package that construction as an *actual system embedding*,
checking all four commuting squares on the two vector-space sorts.

For the target system, the source of each named partial map is the
whole perfect pairing, its domain embedding is the identity, and
its range embedding is the corresponding total automorphism.

This establishes the cofinality input to the Kechris--Rosendal
argument in the same system category used by the JEP/WAP transfer.
It does not prove amalgamation of arbitrary perfect-total systems.
-/

namespace SuccessorTree.NonPrecompact

/-- A finite BANANA n-system is perfect and total when its carrier is
isomorphic, on both sorts, to a finite standard perfect pairing,
and all named partial isomorphisms have full domain and range. -/
def bananaFiniteSystemPerfectTotal {n : ℕ}
    (S : BananaFinitePartialSystem n) : Prop :=
  (∃ k : ℕ,
    ∃ E : BananaMatrixEmbedding S.carrier (perfectBanana k),
      Function.Surjective E.left ∧ Function.Surjective E.right) ∧
  (∀ i : Fin n,
    Function.Surjective (S.domain i).left ∧
    Function.Surjective (S.domain i).right ∧
    Function.Surjective (S.range i).left ∧
    Function.Surjective (S.range i).right)

/-- Every finite BANANA n-system embeds in a finite perfect total
system. The chosen ambient pairing is the same for all n named maps. -/
theorem bananaFiniteSystem_exists_perfect_total_extension
    {n : ℕ} (S : BananaFinitePartialSystem n) :
    ∃ T : BananaFinitePartialSystem n,
      bananaFiniteSystemPerfectTotal T ∧
      Nonempty (BananaFinitePartialSystemEmbedding S T) := by
  let k := S.leftDim + S.rightDim
  let B := perfectBanana k
  obtain ⟨f, H, hL, hR⟩ :=
    exists_common_perfect_completion_total_family
      S.carrier S.sourceLeftDim S.sourceRightDim
      S.source S.domain S.range
  let T : BananaFinitePartialSystem n :=
    { leftDim := k
      rightDim := k
      carrier := B
      sourceLeftDim := fun _ => k
      sourceRightDim := fun _ => k
      source := fun _ => B
      domain := fun _ => BananaMatrixEmbedding.id B
      range := H }
  let e : BananaFinitePartialSystemEmbedding S T :=
    { carrier := f
      source := fun i => BananaMatrixEmbedding.comp f (S.domain i)
      domain_left := by
        intro i x
        rfl
      domain_right := by
        intro i y
        rfl
      range_left := by
        intro i x
        exact (hL i x).symm
      range_right := by
        intro i y
        exact (hR i y).symm }
  refine ⟨T, ?_, ⟨e⟩⟩
  constructor
  · refine ⟨k, BananaMatrixEmbedding.id B, ?_, ?_⟩
    · intro x
      exact ⟨x, rfl⟩
    · intro y
      exact ⟨y, rfl⟩
  · intro i
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      exact ⟨x, rfl⟩
    · intro y
      exact ⟨y, rfl⟩
    · exact Finite.injective_iff_surjective.mp (H i).left_injective
    · exact Finite.injective_iff_surjective.mp (H i).right_injective

end SuccessorTree.NonPrecompact
