import BANANA.NonPrecompact.PrebananaFiveAryCylinderBooleanAlgebra

/-!
# The countable cylinder algebra has an admissible F₂ marking

The marking was defined by a representative at a finite five-ary
word level and proved independent of that representative. The
Boolean-algebra operations are inherited from a Boolean subalgebra
of sets. This module checks the complete finite-additivity axioms
and gives marked bounded-lattice embeddings from every finite stage.

This is the **countable algebraic limit structure**. Proving that
its age is precisely the pre-BANANA class, and establishing the
finite-extension and ultrahomogeneity properties, are further tasks.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- The cylinder limit has at least two distinct Boolean elements. -/
noncomputable instance : Nontrivial PrebananaFiveAryCylinderLimitCarrier := by
  let f := prebananaFiveAryCylinderStageEmbedding 0
  have hne : (f (∅ : Finset (PrebananaFiveAryWord 0))) ≠
      f (Finset.univ : Finset (PrebananaFiveAryWord 0)) := by
    intro h
    have hh : (∅ : Finset (PrebananaFiveAryWord 0)) =
        (Finset.univ : Finset (PrebananaFiveAryWord 0)) :=
      f.injective h
    let w : PrebananaFiveAryWord 0 := fun _ => 0
    have hw : w ∈ (∅ : Finset (PrebananaFiveAryWord 0)) := by
      rw [hh]
      exact Finset.mem_univ w
    simpa using hw
  exact ⟨f (∅ : Finset (PrebananaFiveAryWord 0)),
    f (Finset.univ : Finset (PrebananaFiveAryWord 0)), hne⟩

/-- The parity of the empty cylinder vanishes. -/
theorem prebananaFiveAryCylinderMark_bot :
    prebananaFiveAryCylinderMark
      (⊥ : PrebananaFiveAryCylinderLimitCarrier) = 0 := by
  have h :
      ((⊥ : PrebananaFiveAryCylinderLimitCarrier).val :
        Set PrebananaFiveAryInfiniteWord) =
      prebananaFiveAryCylinder 0
        (∅ : Finset (PrebananaFiveAryWord 0)) := by
    rw [prebananaFiveAryCylinder_val_bot,
      prebananaFiveAryCylinder_empty]
  calc
    prebananaFiveAryCylinderMark
        (⊥ : PrebananaFiveAryCylinderLimitCarrier) =
      (prebananaFiveAryBooleanStage 0).μ
        (∅ : Finset (PrebananaFiveAryWord 0)) :=
          prebananaFiveAryCylinderMark_eq _ 0 ∅ h
    _ = 0 := (prebananaFiveAryBooleanStage 0).μ_bot

/-- The parity of the whole infinite-word space also vanishes. -/
theorem prebananaFiveAryCylinderMark_top :
    prebananaFiveAryCylinderMark
      (⊤ : PrebananaFiveAryCylinderLimitCarrier) = 0 := by
  have h :
      ((⊤ : PrebananaFiveAryCylinderLimitCarrier).val :
        Set PrebananaFiveAryInfiniteWord) =
      prebananaFiveAryCylinder 0
        (Finset.univ : Finset (PrebananaFiveAryWord 0)) := by
    rw [prebananaFiveAryCylinder_val_top,
      prebananaFiveAryCylinder_univ]
  calc
    prebananaFiveAryCylinderMark
        (⊤ : PrebananaFiveAryCylinderLimitCarrier) =
      (prebananaFiveAryBooleanStage 0).μ
        (Finset.univ : Finset (PrebananaFiveAryWord 0)) :=
          prebananaFiveAryCylinderMark_eq _ 0 Finset.univ h
    _ = 0 := (prebananaFiveAryBooleanStage 0).μ_top

/-- Disjoint-additivity of the parity on the actual countable
Boolean algebra of cylinders. The calculation takes place at
one common finite level; no additivity is assumed on the limit. -/
theorem prebananaFiveAryCylinderMark_sup
    (X Y : PrebananaFiveAryCylinderLimitCarrier)
    (hdisjoint : X ⊓ Y = ⊥) :
    prebananaFiveAryCylinderMark (X ⊔ Y) =
      prebananaFiveAryCylinderMark X +
      prebananaFiveAryCylinderMark Y := by
  classical
  obtain ⟨n, s, hs⟩ := X.property
  obtain ⟨m, t, ht⟩ := Y.property
  let N := max n m
  have hn : n ≤ N := le_max_left n m
  have hm : m ≤ N := le_max_right n m
  let sn := prebananaFiveAryRefineTo n N hn s
  let tm := prebananaFiveAryRefineTo m N hm t
  have hx : X.val = prebananaFiveAryCylinder N sn := by
    calc
      X.val = prebananaFiveAryCylinder n s := hs
      _ = prebananaFiveAryCylinder N sn :=
        (prebananaFiveAryRefineTo_cylinder n N hn s).symm
  have hy : Y.val = prebananaFiveAryCylinder N tm := by
    calc
      Y.val = prebananaFiveAryCylinder m t := ht
      _ = prebananaFiveAryCylinder N tm :=
        (prebananaFiveAryRefineTo_cylinder m N hm t).symm
  have hxy :
      (X ⊔ Y).val = prebananaFiveAryCylinder N (sn ∪ tm) := by
    calc
      (X ⊔ Y).val = X.val ∪ Y.val :=
        prebananaFiveAryCylinder_val_sup X Y
      _ = prebananaFiveAryCylinder N sn ∪
          prebananaFiveAryCylinder N tm := by rw [hx, hy]
      _ = prebananaFiveAryCylinder N (sn ∪ tm) :=
        (prebananaFiveAryCylinder_union N sn tm).symm
  have hmeet : sn ∩ tm = ∅ := by
    apply prebananaFiveAryCylinder_injective N
    calc
      prebananaFiveAryCylinder N (sn ∩ tm) =
          prebananaFiveAryCylinder N sn ∩
          prebananaFiveAryCylinder N tm :=
            prebananaFiveAryCylinder_inter N sn tm
      _ = X.val ∩ Y.val := by rw [hx, hy]
      _ = (X ⊓ Y).val :=
        (prebananaFiveAryCylinder_val_inf X Y).symm
      _ = (⊥ : PrebananaFiveAryCylinderLimitCarrier).val :=
        congrArg Subtype.val hdisjoint
      _ = ∅ := prebananaFiveAryCylinder_val_bot
      _ = prebananaFiveAryCylinder N ∅ :=
        (prebananaFiveAryCylinder_empty N).symm
  have hsum :
      (prebananaFiveAryBooleanStage N).μ
        ((sn ∪ tm) : Finset (PrebananaFiveAryWord N)) =
      (prebananaFiveAryBooleanStage N).μ sn +
        (prebananaFiveAryBooleanStage N).μ tm := by
    change (∑ w ∈ sn ∪ tm, prebananaFiveAryWordMark N w) =
      (∑ w ∈ sn, prebananaFiveAryWordMark N w) +
        ∑ w ∈ tm, prebananaFiveAryWordMark N w
    exact Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.mpr hmeet)
  calc
    prebananaFiveAryCylinderMark (X ⊔ Y) =
        (prebananaFiveAryBooleanStage N).μ
          ((sn ∪ tm) : Finset (PrebananaFiveAryWord N)) :=
          prebananaFiveAryCylinderMark_eq _ N _ hxy
    _ = (prebananaFiveAryBooleanStage N).μ sn +
          (prebananaFiveAryBooleanStage N).μ tm := hsum
    _ = prebananaFiveAryCylinderMark X +
          prebananaFiveAryCylinderMark Y := by
            rw [prebananaFiveAryCylinderMark_eq X N sn hx,
              prebananaFiveAryCylinderMark_eq Y N tm hy]

/-- Inclusion of the nth finite marked Boolean stage into the
countable cylinder Boolean algebra as an actual bounded lattice hom. -/
noncomputable def prebananaFiveAryCylinderStageHom (n : ℕ) :
    BoundedLatticeHom
      (prebananaFiveAryBooleanStage n).carrier
      PrebananaFiveAryCylinderLimitCarrier where
  toFun := prebananaFiveAryCylinderStageEmbedding n
  map_bot' := by
    apply Subtype.ext
    exact prebananaFiveAryCylinder_empty n
  map_top' := by
    apply Subtype.ext
    exact prebananaFiveAryCylinder_univ n
  map_sup' := by
    intro s t
    apply Subtype.ext
    exact prebananaFiveAryCylinder_union n s t
  map_inf' := by
    intro s t
    apply Subtype.ext
    exact prebananaFiveAryCylinder_inter n s t

/-- The stage inclusion is injective and preserves the cylinder
marking on every Boolean element. -/
theorem prebananaFiveAryCylinderStageHom_injective (n : ℕ) :
    Function.Injective (prebananaFiveAryCylinderStageHom n) :=
  (prebananaFiveAryCylinderStageEmbedding n).injective

theorem prebananaFiveAryCylinderStageHom_preserves_mark (n : ℕ)
    (s : (prebananaFiveAryBooleanStage n).carrier) :
    prebananaFiveAryCylinderMark
      ((prebananaFiveAryCylinderStageHom n) s) =
      (prebananaFiveAryBooleanStage n).μ s :=
  prebananaFiveAryCylinderStageEmbedding_mark n s

end SuccessorTree.NonPrecompact
