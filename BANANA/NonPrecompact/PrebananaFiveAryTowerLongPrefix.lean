import BANANA.NonPrecompact.PrebananaExplicitFiveAryTower
import BANANA.NonPrecompact.PrebananaFiveAryConcatenation

/-!
# Iterated five-ary tower embeddings are inverse images of long prefixes

The finite pre-BANANA construction embeds a subset of level-n words
into every later Boolean stage by iterating the one-letter prefix
inverse-image map.

This file identifies that iterated embedding exactly with inverse
image under the length-n prefix of a level-(n+k) word, using the
canonical product/concatenation equivalence `Fin.appendEquiv`.

This closes the tower-versus-word representation obligation needed
to turn the finite-extension square into a statement about the
actual iterated tower map.
-/

namespace SuccessorTree.NonPrecompact

/-- The first n letters of an (n+k)-letter five-ary word. -/
def prebananaFiveAryLongPrefix (n k : ℕ) :
    PrebananaFiveAryWord (n + k) → PrebananaFiveAryWord n :=
  fun w => ((Fin.appendEquiv n k).symm w).1

/-- No letters removed means the identity on level-n words. -/
theorem prebananaFiveAryLongPrefix_zero (n : ℕ)
    (w : PrebananaFiveAryWord (n + 0)) :
    prebananaFiveAryLongPrefix n 0 w = w := by
  funext i
  rfl

/-- Dropping the final letter before taking the old prefix does
not alter that prefix. -/
theorem prebananaFiveAryLongPrefix_succ (n k : ℕ)
    (w : PrebananaFiveAryWord (n + (k + 1))) :
    prebananaFiveAryLongPrefix n (k + 1) w =
      prebananaFiveAryLongPrefix n k
        (prebananaFiveAryPrefix (n + k) w) := by
  funext i
  rfl

/-- The *actual iterated* marked Boolean tower embedding from level n
to level n+k is precisely inverse image under the long prefix map.
The identity holds on every subset, not only singletons. -/
theorem prebananaFiveAryTower_iter_eq_prefix
    (n k : ℕ) (s : Finset (PrebananaFiveAryWord n)) :
    (prebananaExplicitFiveAryTower.iterFrom n k).hom s =
      Finset.univ.filter (fun w :
        PrebananaFiveAryWord (n + k) =>
          prebananaFiveAryLongPrefix n k w ∈ s) := by
  classical
  induction k with
  | zero =>
      change s =
        Finset.univ.filter (fun w : PrebananaFiveAryWord (n + 0) =>
          prebananaFiveAryLongPrefix n 0 w ∈ s)
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [prebananaFiveAryLongPrefix_zero]
  | succ k ih =>
      change prebananaFiveAryWordLift (n + k)
          ((prebananaExplicitFiveAryTower.iterFrom n k).hom s) =
        Finset.univ.filter (fun w : PrebananaFiveAryWord (n + (k + 1)) =>
          prebananaFiveAryLongPrefix n (k + 1) w ∈ s)
      rw [ih]
      ext w
      simp only [prebananaFiveAryWordLift, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [prebananaFiveAryLongPrefix_succ]

end SuccessorTree.NonPrecompact
