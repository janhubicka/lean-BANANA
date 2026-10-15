import BANANA.NonPrecompact.PrebananaFiniteBooleanModelEmbeddingCalculus

/-!
# Finite marked Boolean towers

The explicit five-ary pre-BANANA limit starts with a sequence of
finite marked Boolean algebras and injective marking-preserving
embeddings between successive stages.

The identity and composition lemmas give a canonical embedding
from any stage to every later stage. This module records the
reusable abstract tower interface only: it does not assert the
existence of a rich tower or construct its direct limit.

The concrete tower and its extension property are described in
docs/prebanana-five-ary-fraisse-construction.md.
-/

namespace SuccessorTree.NonPrecompact

/-- A sequence of finite pre-BANANA structures connected by genuine
marking-preserving Boolean embeddings. -/
structure PrebananaFiniteBooleanTower where
  stage : ℕ → PrebananaFiniteBooleanModel
  step : ∀ n : ℕ,
    PrebananaFiniteBooleanEmbedding (stage n) (stage (n + 1))

/-- The iterated embedding from stage n to stage n+k.
The zero-step map is the identity and successor-step maps are
composites with the tower's next embedding. -/
def PrebananaFiniteBooleanTower.iterFrom
    (T : PrebananaFiniteBooleanTower) (n : ℕ) :
    (k : ℕ) →
      PrebananaFiniteBooleanEmbedding (T.stage n) (T.stage (n + k))
  | 0 => by
      simpa only [Nat.add_zero] using
        PrebananaFiniteBooleanEmbedding.id (T.stage n)
  | k + 1 => by
      simpa only [Nat.add_succ] using
        (T.step (n + k)).comp (T.iterFrom n k)

/-- Every iterated stage map is injective. -/
theorem PrebananaFiniteBooleanTower.iterFrom_injective
    (T : PrebananaFiniteBooleanTower) (n k : ℕ) :
    Function.Injective (T.iterFrom n k).hom :=
  (T.iterFrom n k).injective

/-- The marking is independent of the stage representing an element. -/
theorem PrebananaFiniteBooleanTower.iterFrom_preserves_mark
    (T : PrebananaFiniteBooleanTower) (n k : ℕ)
    (x : (T.stage n).carrier) :
    (T.stage (n + k)).μ ((T.iterFrom n k).hom x) =
      (T.stage n).μ x :=
  (T.iterFrom n k).preserves_μ x

end SuccessorTree.NonPrecompact
