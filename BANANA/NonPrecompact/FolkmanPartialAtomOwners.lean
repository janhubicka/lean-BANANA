import BANANA.NonPrecompact.PrebananaAbstractBooleanEmbeddingMap
import BANANA.NonPrecompact.PrebananaPowersetMapPartitions

/-!
# Partial atom owners for non-unital finite Boolean-ring embeddings

A homomorphism of finite powerset Boolean rings is an inverse-image
map of a partial function from target atoms to source atoms.  The
difference from pre-BANANA is that some target atoms have no owner.

The proof is a non-unital adaptation of the already verified
pre-BANANA atom-partition reconstruction: singleton images are
pairwise disjoint, cover each image, but need not cover the full
target atom set.  Injectivity forces every source atom to have at
least one target representative.

The abstract bridge uses the existing canonical atom-powerset
representation of arbitrary finite Boolean algebras.  The map is
required to preserve bottom, joins and meets, but NOT top.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Every injective finite powerset map preserving empty, union and
intersection is the inverse-image map of an Option-valued atom owner.
The source fibres are all nonempty; target atoms outside the image
of the source top are assigned none.  No unitality is assumed. -/
theorem folkman_exists_partialOwner_of_powersetEmbedding
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (F : Finset ι → Finset κ)
    (hbot : F ∅ = ∅)
    (hsup : ∀ s t : Finset ι, F (s ∪ t) = F s ∪ F t)
    (hinf : ∀ s t : Finset ι, F (s ∩ t) = F s ∩ F t)
    (hinj : Function.Injective F) :
    ∃ part : κ → Option ι,
      (∀ i : ι, ∃ b : κ, part b = some i) ∧
      (∀ s : Finset ι,
        F s = Finset.univ.filter
          (fun b => ∃ i ∈ s, part b = some i)) := by
  classical
  have hsingletons (s : Finset ι) :
      F s = s.biUnion (fun i => F {i}) := by
    induction s using Finset.induction_on with
    | empty =>
        simpa using hbot
    | @insert i s hi ih =>
        calc
          F (insert i s) = F ({i} ∪ s) := by
            rw [Finset.singleton_union]
          _ = F {i} ∪ F s := hsup _ _
          _ = (insert i s).biUnion (fun j => F {j}) := by
            simp only [Finset.biUnion_insert]
            rw [ih]
  have hunique (b : κ) (i j : ι)
      (hbi : b ∈ F {i}) (hbj : b ∈ F {j}) : i = j := by
    by_contra hne
    have hboth : b ∈ F ({i} ∩ {j}) := by
      rw [hinf]
      exact Finset.mem_inter.mpr ⟨hbi, hbj⟩
    have hnone : ({i} : Finset ι) ∩ {j} = ∅ := by
      simp [hne]
    rw [hnone, hbot] at hboth
    simp at hboth
  have hnonempty (i : ι) : (F {i}).Nonempty := by
    by_contra hempty
    have he : F ({i} : Finset ι) = ∅ := by
      simpa using hempty
    have hsame : F ({i} : Finset ι) = F ∅ := by
      rw [hbot]
      exact he
    have hsingle : ({i} : Finset ι) = ∅ := hinj hsame
    have hi : i ∈ (∅ : Finset ι) := by
      rw [← hsingle]
      simp
    simp at hi
  let part : κ → Option ι := fun b =>
    if h : ∃ i : ι, b ∈ F {i}
    then some (Classical.choose h)
    else none
  have hpart_iff (b : κ) (i : ι) :
      part b = some i ↔ b ∈ F {i} := by
    by_cases hex : ∃ j : ι, b ∈ F {j}
    · have hc : b ∈ F {Classical.choose hex} :=
        Classical.choose_spec hex
      constructor
      · intro he
        have heq : Classical.choose hex = i :=
          Option.some.inj (by simpa only [part, dif_pos hex] using he)
        simpa [heq] using hc
      · intro hb
        have heq : Classical.choose hex = i :=
          hunique b (Classical.choose hex) i hc hb
        simp only [part, dif_pos hex, heq]
    · constructor
      · intro he
        have hnone : part b = none := by
          simp only [part, dif_neg hex]
        rw [hnone] at he
        cases he
      · intro hb
        exact (hex ⟨i, hb⟩).elim
  have hmem (s : Finset ι) (b : κ) :
      b ∈ F s ↔ ∃ i ∈ s, part b = some i := by
    rw [hsingletons]
    constructor
    · intro hb
      rcases Finset.mem_biUnion.mp hb with ⟨i, hi, hbi⟩
      exact ⟨i, hi, (hpart_iff b i).mpr hbi⟩
    · rintro ⟨i, hi, hbi⟩
      exact Finset.mem_biUnion.mpr
        ⟨i, hi, (hpart_iff b i).mp hbi⟩
  refine ⟨part, ?_, ?_⟩
  · intro i
    obtain ⟨b, hb⟩ := hnonempty i
    exact ⟨b, (hpart_iff b i).mpr hb⟩
  · intro s
    ext b
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (hmem s b)

/-- An arbitrary injective *non-unital* map of finite Boolean
algebras preserving bottom, joins and meets determines a partial
atom owner from target atoms to source atoms, with nonempty fibres.
This makes no assumption that the source top maps to the target top. -/
theorem folkmanAbstractEmbedding_exists_partialAtomOwner
    (α β : Type*)
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (φ : α → β)
    (hinj : Function.Injective φ)
    (hbot : φ ⊥ = ⊥)
    (hsup : ∀ x y : α, φ (x ⊔ y) = φ x ⊔ φ y)
    (hinf : ∀ x y : α, φ (x ⊓ y) = φ x ⊓ φ y) :
    ∃ part : PrebananaAbstractAtoms β → Option (PrebananaAbstractAtoms α),
      (∀ a : PrebananaAbstractAtoms α,
        ∃ b : PrebananaAbstractAtoms β, part b = some a) ∧
      (∀ s : Finset (PrebananaAbstractAtoms α),
        prebananaAbstractPowersetMap φ s =
          Finset.univ.filter (fun b => ∃ a ∈ s, part b = some a)) := by
  classical
  exact folkman_exists_partialOwner_of_powersetEmbedding
    (prebananaAbstractPowersetMap φ)
    (prebananaAbstractPowersetMap_empty φ hbot)
    (prebananaAbstractPowersetMap_union φ hsup)
    (prebananaAbstractPowersetMap_inter φ hinf)
    (prebananaAbstractPowersetMap_injective φ hinj)

end SuccessorTree.NonPrecompact
