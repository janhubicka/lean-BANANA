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
  let W := PrebananaFiveAryWord n
  let μW : Finset W → F2 :=
    fun s => ∑ w ∈ s, prebananaFiveAryWordMark n w
  let φ : A.carrier → Finset W := fun x => f.hom x
  have hbot : φ ⊥ = ⊥ := by
    change f.hom (⊥ : A.carrier) = (∅ : Finset W)
    exact map_bot f.hom
  have htop : φ ⊤ = ⊤ := by
    change f.hom (⊤ : A.carrier) = (Finset.univ : Finset W)
    exact map_top f.hom
  have hsup (x y : A.carrier) :
      φ (x ⊔ y) = φ x ⊔ φ y := by
    change f.hom (x ⊔ y) = f.hom x ∪ f.hom y
    exact map_sup f.hom x y
  have hinf (x y : A.carrier) :
      φ (x ⊓ y) = φ x ⊓ φ y := by
    change f.hom (x ⊓ y) = f.hom x ∩ f.hom y
    exact map_inf f.hom x y
  have hmark (x : A.carrier) : μW (φ x) = A.μ x := by
    change (prebananaFiveAryBooleanStage n).μ (f.hom x) = A.μ x
    exact f.preserves_μ x
  have hadd (s t : Finset W) (hst : s ⊓ t = ⊥) :
      μW (s ⊔ t) = μW s + μW t := by
    change (∑ w ∈ s ∪ t, prebananaFiveAryWordMark n w) =
      (∑ w ∈ s, prebananaFiveAryWordMark n w) +
      (∑ w ∈ t, prebananaFiveAryWordMark n w)
    exact Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.mpr hst)
  obtain ⟨part, hsurj, _, hfibre⟩ :=
    prebananaAbstractEmbedding_exists_literalMarkedAtomPartition
      A.carrier (Finset W) A.μ μW
      (by simp [μW]) hadd φ f.injective
      hbot htop hsup hinf hmark
  let e : PrebananaAbstractAtoms (Finset W) ≃ W :=
    prebananaFinitePowersetAtomEquiv W
  let source : W → PrebananaAbstractAtoms A.carrier :=
    fun w => part (e.symm w)
  have hs : Function.Surjective source := by
    intro a
    obtain ⟨b, hb⟩ := hsurj a
    refine ⟨e b, ?_⟩
    change part (e.symm (e b)) = a
    rw [e.symm_apply_apply]
    exact hb
  refine ⟨source, hs, ?_⟩
  intro a
  calc
    (∑ w : W, if source w = a then
      prebananaFiveAryWordMark n w else 0) =
      ∑ b : PrebananaAbstractAtoms (Finset W),
        if part b = a then
          (prebananaFiveAryBooleanStage n).μ (b : Finset W) else 0 :=
            prebananaFiveAryStageAtom_fibreSum n
              (PrebananaAbstractAtoms A.carrier) part a
    _ = ∑ b ∈ (Finset.univ : Finset
        (PrebananaAbstractAtoms (Finset W))).filter
        (fun b => part b = a), μW (b : Finset W) := by
          simp [μW, prebananaFiveAryBooleanStage, Finset.sum_filter]
    _ = A.μ (a : A.carrier) := hfibre a

/-- Given two marked embeddings out of an arbitrary finite base,
one into an arbitrary finite target and one into a five-ary stage,
their induced atom projections have equal marking totals separately
in *every* base-atom fibre. This is the exact hypothesis required by
the canonical finite-extension construction. -/
theorem prebananaFiniteExtension_exists_compatibleAtomPartitions
    (A B : PrebananaFiniteBooleanModel) (n : ℕ)
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
          simpa [Finset.sum_filter] using (htargetMark a).symm

end SuccessorTree.NonPrecompact
