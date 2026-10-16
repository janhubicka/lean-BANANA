import BANANA.NonPrecompact.PrebananaFinitePowersetAtoms
import BANANA.NonPrecompact.PrebananaAbstractMarkedPartitions

/-!
# Atom partitions of abstract embeddings into finite five-ary stages

A genuine marked Boolean embedding of an arbitrary finite
pre-BANANA structure into a finite five-ary stage determines a
surjective map from the *literal level-n words* onto the
abstract source atoms. The F₂-mark of each old atom is precisely
the total mark of the words in its fibre.

The abstract partition theorem already supplies a surjection
between the abstract atoms of two finite Boolean algebras.
The finite-powerset atom equivalence converts the stage atoms to
literal words and preserves every fibre-mark sum.

This is the source-atom component needed to transport the
canonical finite-extension theorem to arbitrary finite Boolean
algebras. Compatibility of the full Boolean-element maps will be
verified separately.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- Any marked embedding from a finite Boolean model into the actual
five-ary stage induces a surjective word-atom projection with
exact per-atom F₂ marking. -/
theorem prebananaFiniteStageEmbedding_exists_wordPartition
    (A : PrebananaFiniteBooleanModel)
    (n : ℕ)
    [DecidableEq (PrebananaAbstractAtoms A.carrier)]
    (f : PrebananaFiniteBooleanEmbedding
      A (prebananaFiveAryBooleanStage n)) :
    ∃ source : PrebananaFiveAryWord n →
        PrebananaAbstractAtoms A.carrier,
      Function.Surjective source ∧
      ∀ a : PrebananaAbstractAtoms A.carrier,
        (∑ w : PrebananaFiveAryWord n,
          if source w = a then prebananaFiveAryWordMark n w else 0) =
          A.μ (a : A.carrier) := by
  classical
  let S : PrebananaFiniteBooleanModel := prebananaFiveAryBooleanStage n
  obtain ⟨part, hsurj, _, hmark⟩ :=
    prebananaAbstractEmbedding_exists_literalMarkedAtomPartition
      A.carrier S.carrier A.μ S.μ
      S.μ_bot S.μ_add f.hom f.injective
      (map_bot f.hom) (map_top f.hom)
      (fun x y => map_sup f.hom x y)
      (fun x y => map_inf f.hom x y)
      f.preserves_μ
  let e : PrebananaAbstractAtoms S.carrier ≃
      PrebananaFiveAryWord n := by
    dsimp [S, prebananaFiveAryBooleanStage]
    exact prebananaFinitePowersetAtomEquiv (PrebananaFiveAryWord n)
  let source : PrebananaFiveAryWord n →
      PrebananaAbstractAtoms A.carrier :=
    fun w => part (e.symm w)
  have hsource : Function.Surjective source := by
    intro a
    obtain ⟨b, hb⟩ := hsurj a
    refine ⟨e b, ?_⟩
    change part (e.symm (e b)) = a
    rw [e.symm_apply_apply]
    exact hb
  refine ⟨source, hsource, ?_⟩
  intro a
  calc
    (∑ w : PrebananaFiveAryWord n,
      if source w = a then prebananaFiveAryWordMark n w else 0) =
        ∑ b : PrebananaAbstractAtoms S.carrier,
          if part b = a then S.μ (b : S.carrier) else 0 := by
          let partW : PrebananaAbstractAtoms (Finset (PrebananaFiveAryWord n)) →
              PrebananaAbstractAtoms A.carrier := by
            simpa [S, prebananaFiveAryBooleanStage] using part
          have h := prebananaFiveAryStageAtom_fibreSum n
            (PrebananaAbstractAtoms A.carrier) partW a
          simpa [partW, S, prebananaFiveAryBooleanStage] using h
    _ = A.μ (a : A.carrier) := by
          simpa only [Finset.sum_filter] using hmark a


/-- Given two marked embeddings out of an arbitrary finite base,
one into an arbitrary finite target and one into a five-ary stage,
their induced atom projections have equal marking totals separately
in *every* base-atom fibre. This is the exact hypothesis required by
the canonical finite-extension construction. -/
theorem prebananaFiniteExtension_exists_compatibleAtomPartitions
    (A B : PrebananaFiniteBooleanModel) (n : ℕ)
    [DecidableEq (PrebananaAbstractAtoms A.carrier)]
    [Fintype (PrebananaAbstractAtoms B.carrier)]
    (f : PrebananaFiniteBooleanEmbedding A B)
    (e : PrebananaFiniteBooleanEmbedding
      A (prebananaFiveAryBooleanStage n)) :
    ∃ source : PrebananaFiveAryWord n →
        PrebananaAbstractAtoms A.carrier,
      ∃ target : PrebananaAbstractAtoms B.carrier →
          PrebananaAbstractAtoms A.carrier,
        Function.Surjective source ∧
        Function.Surjective target ∧
        ∀ a : PrebananaAbstractAtoms A.carrier,
          (∑ w : PrebananaFiveAryWord n,
            if source w = a then prebananaFiveAryWordMark n w else 0) =
          ∑ b : PrebananaAbstractAtoms B.carrier,
            if target b = a then B.μ (b : B.carrier) else 0 := by
  classical
  obtain ⟨source, hsurj, hsourceMark⟩ :=
    prebananaFiniteStageEmbedding_exists_wordPartition A n e
  obtain ⟨target, htsurj, _, htargetMark⟩ :=
    prebananaAbstractEmbedding_exists_literalMarkedAtomPartition
      A.carrier B.carrier A.μ B.μ
      B.μ_bot B.μ_add f.hom f.injective
      (map_bot f.hom) (map_top f.hom)
      (fun x y => map_sup f.hom x y)
      (fun x y => map_inf f.hom x y)
      f.preserves_μ
  refine ⟨source, target, hsurj, htsurj, ?_⟩
  intro a
  calc
    (∑ w : PrebananaFiveAryWord n,
      if source w = a then prebananaFiveAryWordMark n w else 0) =
        A.μ (a : A.carrier) := hsourceMark a
    _ = ∑ b : PrebananaAbstractAtoms B.carrier,
        if target b = a then B.μ (b : B.carrier) else 0 := by
          convert (htargetMark a).symm using 1
          · apply Finset.sum_congr
            · ext b
              simp
            · intro b hb
              rfl

end SuccessorTree.NonPrecompact
