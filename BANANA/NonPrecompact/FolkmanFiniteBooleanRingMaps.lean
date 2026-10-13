import BANANA.NonPrecompact.FolkmanAtomAmalgam

/-!
# Finite non-unital Boolean-ring maps in the Folkman atom amalgam

Represent finite Boolean rings as finite subsets of their atoms,
with symmetric difference as addition and intersection as
multiplication. Source atoms map either to rows/columns of the
compatible-pair grids or to distinct private points.

This file verifies preservation of the actual Boolean-ring
operations, injectivity (under nonempty base fibres), and strong
intersection of the two finite-subset images. The separate bilinear
extension is already kernel-checked in FolkmanBilinearExtension.
A fully packaged two-sorted Fraïssé amalgamation theorem still
requires combining these interfaces.
-/

namespace SuccessorTree.NonPrecompact

/-- The left Boolean-ring embedding on finite subsets of atoms. -/
noncomputable def folkmanFinsetLeftMap
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (SB : Finset B) : Finset (FolkmanAtomAmalgam f g) := by
  classical
  exact Finset.univ.filter (folkmanLeftImage (↑SB : Set B))

/-- The right Boolean-ring embedding on finite subsets of atoms. -/
noncomputable def folkmanFinsetRightMap
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (SC : Finset C) : Finset (FolkmanAtomAmalgam f g) := by
  classical
  exact Finset.univ.filter (folkmanRightImage (↑SC : Set C))

@[simp] theorem folkmanFinsetLeftMap_mem
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (SB : Finset B) (p : FolkmanAtomAmalgam f g) :
    p ∈ folkmanFinsetLeftMap f g SB ↔
      folkmanLeftImage (↑SB : Set B) p := by
  classical
  simp [folkmanFinsetLeftMap]

@[simp] theorem folkmanFinsetRightMap_mem
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (SC : Finset C) (p : FolkmanAtomAmalgam f g) :
    p ∈ folkmanFinsetRightMap f g SC ↔
      folkmanRightImage (↑SC : Set C) p := by
  classical
  simp [folkmanFinsetRightMap]

/-- Left maps preserve the zero of the non-unital Boolean ring. -/
theorem folkmanFinsetLeftMap_empty
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A) :
    folkmanFinsetLeftMap f g ∅ = ∅ := by
  classical
  ext p
  cases p with
  | inl p => simp [folkmanLeftImage]
  | inr p =>
      cases p with
      | inl b => simp [folkmanLeftImage]
      | inr c => simp [folkmanLeftImage]

/-- Left maps preserve binary unions. -/
theorem folkmanFinsetLeftMap_union
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (s t : Finset B) :
    folkmanFinsetLeftMap f g (s ∪ t) =
      folkmanFinsetLeftMap f g s ∪ folkmanFinsetLeftMap f g t := by
  classical
  ext p
  cases p with
  | inl p => simp [folkmanLeftImage]
  | inr p =>
      cases p with
      | inl b => simp [folkmanLeftImage]
      | inr c => simp [folkmanLeftImage]

/-- Left maps preserve multiplication (intersection). -/
theorem folkmanFinsetLeftMap_inter
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (s t : Finset B) :
    folkmanFinsetLeftMap f g (s ∩ t) =
      folkmanFinsetLeftMap f g s ∩ folkmanFinsetLeftMap f g t := by
  classical
  ext p
  cases p with
  | inl p => simp [folkmanLeftImage]
  | inr p =>
      cases p with
      | inl b => simp [folkmanLeftImage]
      | inr c => simp [folkmanLeftImage]

/-- Left maps preserve addition (symmetric difference). -/
theorem folkmanFinsetLeftMap_symmDiff
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (s t : Finset B) :
    folkmanFinsetLeftMap f g (s ∆ t) =
      folkmanFinsetLeftMap f g s ∆ folkmanFinsetLeftMap f g t := by
  classical
  ext p
  cases p with
  | inl p => simp [folkmanLeftImage, Finset.mem_symmDiff]
  | inr p =>
      cases p with
      | inl b => simp [folkmanLeftImage, Finset.mem_symmDiff]
      | inr c => simp [folkmanLeftImage, Finset.mem_symmDiff]

/-- The symmetric ring-operation statements for the right embedding. -/
theorem folkmanFinsetRightMap_empty
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A) :
    folkmanFinsetRightMap f g ∅ = ∅ := by
  classical
  ext p
  cases p with
  | inl p => simp [folkmanRightImage]
  | inr p =>
      cases p with
      | inl b => simp [folkmanRightImage]
      | inr c => simp [folkmanRightImage]

theorem folkmanFinsetRightMap_union
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (s t : Finset C) :
    folkmanFinsetRightMap f g (s ∪ t) =
      folkmanFinsetRightMap f g s ∪ folkmanFinsetRightMap f g t := by
  classical
  ext p
  cases p with
  | inl p => simp [folkmanRightImage]
  | inr p =>
      cases p with
      | inl b => simp [folkmanRightImage]
      | inr c => simp [folkmanRightImage]

theorem folkmanFinsetRightMap_inter
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (s t : Finset C) :
    folkmanFinsetRightMap f g (s ∩ t) =
      folkmanFinsetRightMap f g s ∩ folkmanFinsetRightMap f g t := by
  classical
  ext p
  cases p with
  | inl p => simp [folkmanRightImage]
  | inr p =>
      cases p with
      | inl b => simp [folkmanRightImage]
      | inr c => simp [folkmanRightImage]

theorem folkmanFinsetRightMap_symmDiff
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (s t : Finset C) :
    folkmanFinsetRightMap f g (s ∆ t) =
      folkmanFinsetRightMap f g s ∆ folkmanFinsetRightMap f g t := by
  classical
  ext p
  cases p with
  | inl p => simp [folkmanRightImage, Finset.mem_symmDiff]
  | inr p =>
      cases p with
      | inl b => simp [folkmanRightImage, Finset.mem_symmDiff]
      | inr c => simp [folkmanRightImage, Finset.mem_symmDiff]

/-- Nonempty opposite base fibres make the left Boolean-ring map
injective; private points make the outside atoms injective as well. -/
theorem folkmanFinsetLeftMap_injective
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (hg : ∀ a : A, ∃ c : C, g c = some a) :
    Function.Injective (folkmanFinsetLeftMap f g) := by
  classical
  intro s t heq
  ext b
  by_cases hb : f b = none
  · let p : FolkmanAtomAmalgam f g := .inr (.inl ⟨b, hb⟩)
    have hm : p ∈ folkmanFinsetLeftMap f g s ↔
        p ∈ folkmanFinsetLeftMap f g t := by rw [heq]
    simpa [p, folkmanLeftImage] using hm
  · obtain ⟨a, ha⟩ : ∃ a : A, f b = some a := by
      cases h : f b with
      | none => exact False.elim (hb h)
      | some a => exact ⟨a, h⟩
    obtain ⟨c, hc⟩ := hg a
    let p : FolkmanAtomAmalgam f g := .inl ⟨(b, c), ⟨a, ha, hc⟩⟩
    have hm : p ∈ folkmanFinsetLeftMap f g s ↔
        p ∈ folkmanFinsetLeftMap f g t := by rw [heq]
    simpa [p, folkmanLeftImage] using hm

/-- Nonempty opposite base fibres make the right Boolean-ring map
injective, while its outside atoms have distinct private points. -/
theorem folkmanFinsetRightMap_injective
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (hf : ∀ a : A, ∃ b : B, f b = some a) :
    Function.Injective (folkmanFinsetRightMap f g) := by
  classical
  intro s t heq
  ext c
  by_cases hc : g c = none
  · let p : FolkmanAtomAmalgam f g := .inr (.inr ⟨c, hc⟩)
    have hm : p ∈ folkmanFinsetRightMap f g s ↔
        p ∈ folkmanFinsetRightMap f g t := by rw [heq]
    simpa [p, folkmanRightImage] using hm
  · obtain ⟨a, ha⟩ : ∃ a : A, g c = some a := by
      cases h : g c with
      | none => exact False.elim (hc h)
      | some a => exact ⟨a, h⟩
    obtain ⟨b, hb⟩ := hf a
    let p : FolkmanAtomAmalgam f g := .inl ⟨(b, c), ⟨a, hb, ha⟩⟩
    have hm : p ∈ folkmanFinsetRightMap f g s ↔
        p ∈ folkmanFinsetRightMap f g t := by rw [heq]
    simpa [p, folkmanRightImage] using hm

/-- The two images have the strong intersection described in the
circulation proof, including the private outside points. -/
theorem folkmanFinsetImages_strong_intersection
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (hf : ∀ a : A, ∃ b : B, f b = some a)
    (hg : ∀ a : A, ∃ c : C, g c = some a)
    (SB : Finset B) (SC : Finset C)
    (heq : folkmanFinsetLeftMap f g SB =
      folkmanFinsetRightMap f g SC) :
    ∃ SA : Set A,
      (∀ b a, f b = some a → (b ∈ SB ↔ a ∈ SA)) ∧
      (∀ b, f b = none → b ∉ SB) ∧
      (∀ c a, g c = some a → (c ∈ SC ↔ a ∈ SA)) ∧
      (∀ c, g c = none → c ∉ SC) := by
  classical
  have hpred : ∀ p : FolkmanAtomAmalgam f g,
      folkmanLeftImage (↑SB : Set B) p ↔
      folkmanRightImage (↑SC : Set C) p := by
    intro p
    have hm : p ∈ folkmanFinsetLeftMap f g SB ↔
        p ∈ folkmanFinsetRightMap f g SC := by rw [heq]
    simpa using hm
  exact exists_common_subset_of_folkmanAtomAmalgam
    f g hf hg (↑SB : Set B) (↑SC : Set C) hpred

end SuccessorTree.NonPrecompact
