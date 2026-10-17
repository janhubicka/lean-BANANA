import BANANA.NonPrecompact.PrebananaFiveAryCylinderFiniteFamily
import BANANA.NonPrecompact.PrebananaFiveAryCylinderBooleanAlgebra
import BANANA.NonPrecompact.PrebananaAbstractClassEPPA

/-!
# Factor finite marked embeddings of cylinders through a finite stage

Any actual finite marked Boolean algebra mapped into the countable
cylinder algebra has only finitely many elements. The simultaneous
finite-family lemma presents all their images at one common finite
word level. Because the cylinder map of that level is injective,
the resulting representative map preserves the Boolean operations.
It also preserves the prescribed F₂ marking.

Thus a finite marked embedding into the cylinder algebra factors
through one *genuine finite marked Boolean embedding* into an
actual five-ary stage. The proof does not assume that the countable
cylinder algebra is already homogeneous.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- A genuine bounded-lattice embedding of a finite marked Boolean
algebra into the cylinder Boolean algebra, preserving the
stage-independent F₂ marking, factors through one finite five-ary
stage. All Boolean-element maps commute exactly, not just the
atom-marking sums. -/
theorem prebananaFiveAryCylinder_finiteEmbedding_factor
    (A : PrebananaFiniteBooleanModel)
    (e : BoundedLatticeHom A.carrier PrebananaFiveAryCylinderLimitCarrier)
    (hinj : Function.Injective e)
    (hmark : ∀ x : A.carrier,
      prebananaFiveAryCylinderMark (e x) = A.μ x) :
    ∃ n : ℕ,
      ∃ g : PrebananaFiniteBooleanEmbedding A
        (prebananaFiveAryBooleanStage n),
        ∀ x : A.carrier,
          prebananaFiveAryCylinderStageEmbedding n (g.hom x) = e x := by
  classical
  obtain ⟨n, s, hs⟩ :=
    prebananaFiveAryCylinder_finiteFamily_commonStage
      (fun x : A.carrier => e x)
  have hv (x : A.carrier) :
      prebananaFiveAryCylinder n (s x) = (e x).val :=
    congrArg Subtype.val (hs x)
  have hbot : s (⊥ : A.carrier) =
      (∅ : Finset (PrebananaFiveAryWord n)) := by
    apply prebananaFiveAryCylinder_injective n
    calc
      prebananaFiveAryCylinder n (s ⊥) = (e ⊥).val := hv _
      _ = (⊥ : PrebananaFiveAryCylinderLimitCarrier).val :=
        congrArg Subtype.val (map_bot e)
      _ = ∅ := prebananaFiveAryCylinder_val_bot
      _ = prebananaFiveAryCylinder n ∅ :=
        (prebananaFiveAryCylinder_empty n).symm
  have htop : s (⊤ : A.carrier) =
      (Finset.univ : Finset (PrebananaFiveAryWord n)) := by
    apply prebananaFiveAryCylinder_injective n
    calc
      prebananaFiveAryCylinder n (s ⊤) = (e ⊤).val := hv _
      _ = (⊤ : PrebananaFiveAryCylinderLimitCarrier).val :=
        congrArg Subtype.val (map_top e)
      _ = Set.univ := prebananaFiveAryCylinder_val_top
      _ = prebananaFiveAryCylinder n Finset.univ :=
        (prebananaFiveAryCylinder_univ n).symm
  have hsup (x y : A.carrier) :
      s (x ⊔ y) = s x ∪ s y := by
    apply prebananaFiveAryCylinder_injective n
    calc
      prebananaFiveAryCylinder n (s (x ⊔ y)) =
          (e (x ⊔ y)).val := hv _
      _ = (e x ⊔ e y).val :=
        congrArg Subtype.val (map_sup e x y)
      _ = (e x).val ∪ (e y).val :=
        prebananaFiveAryCylinder_val_sup (e x) (e y)
      _ = prebananaFiveAryCylinder n (s x) ∪
          prebananaFiveAryCylinder n (s y) := by rw [hv x, hv y]
      _ = prebananaFiveAryCylinder n (s x ∪ s y) :=
        (prebananaFiveAryCylinder_union n (s x) (s y)).symm
  have hinf (x y : A.carrier) :
      s (x ⊓ y) = s x ∩ s y := by
    apply prebananaFiveAryCylinder_injective n
    calc
      prebananaFiveAryCylinder n (s (x ⊓ y)) =
          (e (x ⊓ y)).val := hv _
      _ = (e x ⊓ e y).val :=
        congrArg Subtype.val (map_inf e x y)
      _ = (e x).val ∩ (e y).val :=
        prebananaFiveAryCylinder_val_inf (e x) (e y)
      _ = prebananaFiveAryCylinder n (s x) ∩
          prebananaFiveAryCylinder n (s y) := by rw [hv x, hv y]
      _ = prebananaFiveAryCylinder n (s x ∩ s y) :=
        (prebananaFiveAryCylinder_inter n (s x) (s y)).symm
  let ghom : BoundedLatticeHom A.carrier
      (prebananaFiveAryBooleanStage n).carrier where
    toFun := s
    map_bot' := by
      change s (⊥ : A.carrier) = (∅ : Finset (PrebananaFiveAryWord n))
      exact hbot
    map_top' := by
      change s (⊤ : A.carrier) =
        (Finset.univ : Finset (PrebananaFiveAryWord n))
      exact htop
    map_sup' := by
      intro x y
      change s (x ⊔ y) = s x ∪ s y
      exact hsup x y
    map_inf' := by
      intro x y
      change s (x ⊓ y) = s x ∩ s y
      exact hinf x y
  have hgInj : Function.Injective ghom := by
    intro x y hxy
    apply hinj
    calc
      e x = prebananaFiveAryCylinderStageEmbedding n (s x) := (hs x).symm
      _ = prebananaFiveAryCylinderStageEmbedding n (s y) := by
        exact congrArg (prebananaFiveAryCylinderStageEmbedding n) hxy
      _ = e y := hs y
  have hgMark (x : A.carrier) :
      (prebananaFiveAryBooleanStage n).μ (ghom x) = A.μ x := by
    calc
      (prebananaFiveAryBooleanStage n).μ (ghom x) =
          prebananaFiveAryCylinderMark
            (prebananaFiveAryCylinderStageEmbedding n (s x)) :=
          (prebananaFiveAryCylinderStageEmbedding_mark n (s x)).symm
      _ = prebananaFiveAryCylinderMark (e x) :=
          congrArg prebananaFiveAryCylinderMark (hs x)
      _ = A.μ x := hmark x
  let g : PrebananaFiniteBooleanEmbedding A
      (prebananaFiveAryBooleanStage n) where
    hom := ghom
    injective := hgInj
    preserves_μ := hgMark
  refine ⟨n, g, ?_⟩
  intro x
  exact hs x

end SuccessorTree.NonPrecompact
