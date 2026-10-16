import BANANA.NonPrecompact.PrebananaFiveAryCylinderLimitCarrier
import BANANA.NonPrecompact.PrebananaFiveAryTowerLongPrefix

/-!
# Compatibility of finite-prefix cylinders with the five-ary tower

The nth finite stage embeds as cylinder subsets of infinite words.
Refining an element along the actual iterated marked tower embeddings
does not change its cylinder subset. This is the first step towards
the well-defined limit marking and a common-stage Boolean subalgebra.

The result concerns sets and stage maps only; it is not yet a
construction of the full Fraïssé limit.
-/

namespace SuccessorTree.NonPrecompact

/-- The length-n prefix of the length-(n+k) prefix of an infinite
five-ary branch is just the length-n prefix of the branch. -/
theorem prebananaFiveAryInfinitePrefix_longPrefix (n k : ℕ)
    (w : PrebananaFiveAryInfiniteWord) :
    prebananaFiveAryLongPrefix n k
      (prebananaFiveAryInfinitePrefix (n + k) w) =
    prebananaFiveAryInfinitePrefix n w := by
  funext i
  rfl

/-- An element and its image at any later five-ary stage represent
exactly the same subset of infinite branches. -/
theorem prebananaFiveAryCylinder_iter (n k : ℕ)
    (s : Finset (PrebananaFiveAryWord n)) :
    prebananaFiveAryCylinder (n + k)
        ((prebananaExplicitFiveAryTower.iterFrom n k).hom s) =
      prebananaFiveAryCylinder n s := by
  have hstage :
      ((prebananaExplicitFiveAryTower.iterFrom n k).hom s :
        Finset (PrebananaFiveAryWord (n + k))) =
      Finset.univ.filter (fun w : PrebananaFiveAryWord (n + k) =>
        prebananaFiveAryLongPrefix n k w ∈ s) :=
    prebananaFiveAryTower_iter_eq_prefix n k s
  calc
    prebananaFiveAryCylinder (n + k)
        ((prebananaExplicitFiveAryTower.iterFrom n k).hom s) =
      prebananaFiveAryCylinder (n + k)
        (Finset.univ.filter (fun w : PrebananaFiveAryWord (n + k) =>
          prebananaFiveAryLongPrefix n k w ∈ s)) :=
            congrArg (prebananaFiveAryCylinder (n + k)) hstage
    _ = prebananaFiveAryCylinder n s := by
          ext w
          simp only [prebananaFiveAryCylinder, Set.mem_setOf_eq,
            Finset.mem_filter, Finset.mem_univ, true_and]
          rw [prebananaFiveAryInfinitePrefix_longPrefix]

/-- The finite-stage embeddings into the cylinder carrier commute
with every iterated marked five-ary tower embedding. -/
theorem prebananaFiveAryCylinderStageEmbedding_iter (n k : ℕ)
    (s : (prebananaFiveAryBooleanStage n).carrier) :
    prebananaFiveAryCylinderStageEmbedding (n + k)
        ((prebananaExplicitFiveAryTower.iterFrom n k).hom s) =
      prebananaFiveAryCylinderStageEmbedding n s := by
  apply Subtype.ext
  exact prebananaFiveAryCylinder_iter n k s

end SuccessorTree.NonPrecompact
