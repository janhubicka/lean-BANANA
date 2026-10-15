import BANANA.NonPrecompact.PrebananaFiveAryWordLiftParity

/-!
# An explicit tower of finite marked Boolean algebras

The nth stage is the Boolean algebra of subsets of n-letter
five-ary words, marked by the recursive parity. Connecting
embeddings are inverse images under the prefix projection.

The previous modules verify the Boolean operations, injectivity,
and preservation of marking. Here they are assembled into a
genuine PrebananaFiniteBooleanTower.

This is not yet a countable direct limit, and no ultrahomogeneity
or finite-extension theorem is claimed.
-/

namespace SuccessorTree.NonPrecompact

/-- The prefix inverse-image map between successive stages is
an injective marking-preserving bounded-lattice homomorphism. -/
noncomputable def prebananaFiveAryBooleanStep (n : ℕ) :
    PrebananaFiniteBooleanEmbedding
      (prebananaFiveAryBooleanStage n)
      (prebananaFiveAryBooleanStage (n + 1)) where
  hom := prebananaFiveAryWordLiftHom n
  injective := prebananaFiveAryWordLiftHom_injective n
  preserves_μ := by
    intro s
    change
      (∑ w ∈ prebananaFiveAryWordLift n s,
        prebananaFiveAryWordMark (n + 1) w) =
      (∑ w ∈ s, prebananaFiveAryWordMark n w)
    exact prebananaFiveAryWordLift_preserves_mark n s

/-- The explicit five-ary sequence, now as a tower of *actual*
finite marked Boolean models with marked embeddings. -/
noncomputable def prebananaExplicitFiveAryTower :
    PrebananaFiniteBooleanTower where
  stage := prebananaFiveAryBooleanStage
  step := prebananaFiveAryBooleanStep

/-- Every later stage receives an injective marking-preserving
embedding from each previous stage. -/
theorem prebananaExplicitFiveAryTower_iter_preserves_mark
    (n k : ℕ)
    (s : (prebananaExplicitFiveAryTower.stage n).carrier) :
    (prebananaExplicitFiveAryTower.stage (n + k)).μ
      ((prebananaExplicitFiveAryTower.iterFrom n k).hom s) =
      (prebananaExplicitFiveAryTower.stage n).μ s :=
  prebananaExplicitFiveAryTower.iterFrom_preserves_mark n k s

end SuccessorTree.NonPrecompact
