import BANANA.NonPrecompact.PrebananaFiniteBooleanRepresentation

/-!
# Recovering atom partitions from embeddings of finite powersets

A unital Boolean embedding between finite powersets is the inverse-image
map of a unique surjection between their atom sets. This is the
converse direction of the atom-partition description used in the
circulation manuscript. The proof works for arbitrary finite index
types and does not assume a linear ordering of atoms.

The next bridge will conjugate an arbitrary finite Boolean-algebra
embedding through the canonical atom-powerset order isomorphisms,
then apply this theorem.
-/

namespace SuccessorTree.NonPrecompact

/-- A finite powerset embedding preserving the four Boolean
operations and injectivity is the inverse-image map of a
surjective atom-partition map. -/
theorem prebanana_exists_atomPartition_of_powersetEmbedding
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (F : Finset ι → Finset κ)
    (hbot : F ∅ = ∅)
    (htop : F Finset.univ = Finset.univ)
    (hsup : ∀ s t : Finset ι,
      F (s ∪ t) = F s ∪ F t)
    (hinf : ∀ s t : Finset ι,
      F (s ∩ t) = F s ∩ F t)
    (hinj : Function.Injective F) :
    ∃ part : κ → ι,
      Function.Surjective part ∧
      ∀ s : Finset ι,
        F s = Finset.univ.filter (fun b => part b ∈ s) := by
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
  have hcover (b : κ) : ∃ i : ι, b ∈ F {i} := by
    have hb : b ∈ F (Finset.univ : Finset ι) := by
      rw [htop]
      simp
    rw [hsingletons] at hb
    rcases Finset.mem_biUnion.mp hb with ⟨i, _, hi⟩
    exact ⟨i, hi⟩
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
  let part : κ → ι := fun b => Classical.choose (hcover b)
  have hpart (b : κ) : b ∈ F {part b} :=
    Classical.choose_spec (hcover b)
  have hmem (s : Finset ι) (b : κ) :
      b ∈ F s ↔ part b ∈ s := by
    rw [hsingletons]
    constructor
    · intro hb
      rcases Finset.mem_biUnion.mp hb with ⟨i, hi, hbi⟩
      rw [hunique b i (part b) hbi (hpart b)] at hi
      exact hi
    · intro hi
      exact Finset.mem_biUnion.mpr
        ⟨part b, hi, hpart b⟩
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
  refine ⟨part, ?_, ?_⟩
  · intro i
    obtain ⟨b, hb⟩ := hnonempty i
    exact ⟨b, (hunique b i (part b) hb (hpart b)).symm⟩
  · intro s
    ext b
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      (hmem s b)

end SuccessorTree.NonPrecompact
