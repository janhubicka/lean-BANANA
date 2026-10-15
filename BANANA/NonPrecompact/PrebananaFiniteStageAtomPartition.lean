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

/-- Any marked embedding from a finite Boolean model into the actual
five-ary stage induces a surjective word-atom projection with
exact per-atom F₂ marking. -/
theorem prebananaFiniteStageEmbedding_exists_wordPartition
    (A : PrebananaFiniteBooleanModel)
    (n : ℕ)
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
  let e : PrebananaAbstractAtoms
      (Finset (PrebananaFiveAryWord n)) ≃
      PrebananaFiveAryWord n :=
    prebananaFinitePowersetAtomEquiv (PrebananaFiveAryWord n)
  let source : PrebananaFiveAryWord n →
      PrebananaAbstractAtoms A.carrier :=
    fun w => part (e.symm w)
  have hsource : Function.Surjective source := by
    intro a
    obtain ⟨b, hb⟩ := hsurj a
    refine ⟨e b, ?_⟩
    simpa [source] using hb
  refine ⟨source, hsource, ?_⟩
  intro a
  calc
    (∑ w : PrebananaFiveAryWord n,
      if source w = a then prebananaFiveAryWordMark n w else 0) =
        ∑ b : PrebananaAbstractAtoms (Finset (PrebananaFiveAryWord n)),
          if part b = a then
            (prebananaFiveAryBooleanStage n).μ
              (b : Finset (PrebananaFiveAryWord n)) else 0 := by
          exact prebananaFiveAryStageAtom_fibreSum n
            (PrebananaAbstractAtoms A.carrier) part a
    _ = ∑ b ∈ (Finset.univ : Finset
          (PrebananaAbstractAtoms S.carrier)).filter
          (fun b => part b = a), S.μ (b : S.carrier) := by
          simp only [Finset.sum_filter]
    _ = A.μ (a : A.carrier) := hmark a

end SuccessorTree.NonPrecompact
