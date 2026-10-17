import BANANA.NonPrecompact.PrebananaFiveAryCylinderTowerCompatibility

/-!
# Stage-independent parity marking on the countable pre-BANANA cylinders

Each cylinder subset of infinite five-ary branches is represented
by a subset of the words of some finite length. A representation
at a larger length is obtained by the genuine marked tower map.

The key point is **uniqueness of the F₂ mark**: two presentations
of the same cylinder can be refined to one common finite level.
Injectivity of that level's cylinder map identifies the two
refinements, and the tower embeddings preserve their markings.

This module establishes stage-independent marking but does not
yet give the cylinder carrier a Boolean-algebra instance or prove
its Fraïssé extension and homogeneity properties.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Transporting a finite word subset along equality of word
lengths does not change its cylinder subset. The two length
variables are independent, so dependent elimination is valid. -/
theorem prebananaFiveAryCylinder_cast
    {a b : ℕ} (h : a = b)
    (s : Finset (PrebananaFiveAryWord a)) :
    prebananaFiveAryCylinder b (h ▸ s) =
      prebananaFiveAryCylinder a s := by
  cases h
  rfl

/-- The same equality transport preserves the marking of
the associated finite Boolean stage. -/
theorem prebananaFiveAryCylinder_cast_mark
    {a b : ℕ} (h : a = b)
    (s : Finset (PrebananaFiveAryWord a)) :
    (prebananaFiveAryBooleanStage b).μ (h ▸ s) =
      (prebananaFiveAryBooleanStage a).μ s := by
  cases h
  rfl

/-- Refine a finite word subset to any later level of the
actual five-ary marked Boolean tower. -/
noncomputable def prebananaFiveAryRefineTo
    (n N : ℕ) (hn : n ≤ N)
    (s : Finset (PrebananaFiveAryWord n)) :
    Finset (PrebananaFiveAryWord N) := by
  have h : n + (N - n) = N := Nat.add_sub_of_le hn
  exact h ▸ (prebananaExplicitFiveAryTower.iterFrom n (N - n)).hom s

/-- Refinement to a later level preserves the represented
cylinder set of infinite branches. -/
theorem prebananaFiveAryRefineTo_cylinder
    (n N : ℕ) (hn : n ≤ N)
    (s : Finset (PrebananaFiveAryWord n)) :
    prebananaFiveAryCylinder N (prebananaFiveAryRefineTo n N hn s) =
      prebananaFiveAryCylinder n s := by
  let k := N - n
  have hN : n + k = N := Nat.add_sub_of_le hn
  let z : Finset (PrebananaFiveAryWord (n + k)) :=
    (prebananaExplicitFiveAryTower.iterFrom n k).hom s
  have htransport :
      prebananaFiveAryCylinder N (prebananaFiveAryRefineTo n N hn s) =
      prebananaFiveAryCylinder (n + k) z := by
    change prebananaFiveAryCylinder N (hN ▸ z) =
      prebananaFiveAryCylinder (n + k) z
    exact prebananaFiveAryCylinder_cast hN z
  exact htransport.trans (prebananaFiveAryCylinder_iter n k s)

/-- Refinement preserves exactly the F₂ marking of the finite
marked Boolean algebra. -/
theorem prebananaFiveAryRefineTo_mark
    (n N : ℕ) (hn : n ≤ N)
    (s : Finset (PrebananaFiveAryWord n)) :
    (prebananaFiveAryBooleanStage N).μ
      (prebananaFiveAryRefineTo n N hn s) =
    (prebananaFiveAryBooleanStage n).μ s := by
  let k := N - n
  have hN : n + k = N := Nat.add_sub_of_le hn
  let z : Finset (PrebananaFiveAryWord (n + k)) :=
    (prebananaExplicitFiveAryTower.iterFrom n k).hom s
  have htransport :
      (prebananaFiveAryBooleanStage N).μ
        (prebananaFiveAryRefineTo n N hn s) =
      (prebananaFiveAryBooleanStage (n + k)).μ z := by
    change (prebananaFiveAryBooleanStage N).μ (hN ▸ z) =
      (prebananaFiveAryBooleanStage (n + k)).μ z
    exact prebananaFiveAryCylinder_cast_mark hN z
  exact htransport.trans
    (prebananaExplicitFiveAryTower_iter_preserves_mark n k s)

/-- Two possibly different-level finite descriptions of exactly the
same cylinder necessarily have identical F₂ markings. -/
theorem prebananaFiveAryCylinder_equal_marks
    (n m : ℕ)
    (s : Finset (PrebananaFiveAryWord n))
    (t : Finset (PrebananaFiveAryWord m))
    (heq : prebananaFiveAryCylinder n s =
      prebananaFiveAryCylinder m t) :
    (prebananaFiveAryBooleanStage n).μ s =
      (prebananaFiveAryBooleanStage m).μ t := by
  let N := max n m
  have hn : n ≤ N := le_max_left n m
  have hm : m ≤ N := le_max_right n m
  have heqN :
      prebananaFiveAryRefineTo n N hn s =
        prebananaFiveAryRefineTo m N hm t := by
    apply prebananaFiveAryCylinder_injective N
    calc
      prebananaFiveAryCylinder N (prebananaFiveAryRefineTo n N hn s) =
          prebananaFiveAryCylinder n s :=
            prebananaFiveAryRefineTo_cylinder n N hn s
      _ = prebananaFiveAryCylinder m t := heq
      _ = prebananaFiveAryCylinder N (prebananaFiveAryRefineTo m N hm t) :=
        (prebananaFiveAryRefineTo_cylinder m N hm t).symm
  calc
    (prebananaFiveAryBooleanStage n).μ s =
        (prebananaFiveAryBooleanStage N).μ
          (prebananaFiveAryRefineTo n N hn s) :=
            (prebananaFiveAryRefineTo_mark n N hn s).symm
    _ = (prebananaFiveAryBooleanStage N).μ
          (prebananaFiveAryRefineTo m N hm t) :=
            congrArg (prebananaFiveAryBooleanStage N).μ heqN
    _ = (prebananaFiveAryBooleanStage m).μ t :=
        prebananaFiveAryRefineTo_mark m N hm t

/-- The unique F₂ marking of a finite-prefix cylinder, obtained
from any finite-stage presentation. -/
noncomputable def prebananaFiveAryCylinderMark
    (X : PrebananaFiveAryCylinderLimitCarrier) : F2 :=
  let n := Classical.choose X.property
  let s := Classical.choose (Classical.choose_spec X.property)
  (prebananaFiveAryBooleanStage n).μ s

/-- The cylinder mark agrees with the mark of **every**
finite-stage representation, not just the chosen one. -/
theorem prebananaFiveAryCylinderMark_eq
    (X : PrebananaFiveAryCylinderLimitCarrier)
    (n : ℕ) (s : Finset (PrebananaFiveAryWord n))
    (h : X.val = prebananaFiveAryCylinder n s) :
    prebananaFiveAryCylinderMark X =
      (prebananaFiveAryBooleanStage n).μ s := by
  classical
  let n' := Classical.choose X.property
  let s' := Classical.choose (Classical.choose_spec X.property)
  have hchosen :
      prebananaFiveAryCylinder n' s' =
        prebananaFiveAryCylinder n s := by
    exact (Classical.choose_spec (Classical.choose_spec X.property)).symm.trans h
  change (prebananaFiveAryBooleanStage n').μ s' =
    (prebananaFiveAryBooleanStage n).μ s
  exact prebananaFiveAryCylinder_equal_marks n' n s' s hchosen

/-- The canonical injection from every finite stage preserves F₂
marking, exactly as required for a marked Boolean limit. -/
theorem prebananaFiveAryCylinderStageEmbedding_mark
    (n : ℕ) (s : (prebananaFiveAryBooleanStage n).carrier) :
    prebananaFiveAryCylinderMark
      (prebananaFiveAryCylinderStageEmbedding n s) =
    (prebananaFiveAryBooleanStage n).μ s := by
  apply prebananaFiveAryCylinderMark_eq _ n s
  rfl

end SuccessorTree.NonPrecompact
