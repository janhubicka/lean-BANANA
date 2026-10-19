import BANANA.NonPrecompact.FolkmanFiniteTwoSortRingDiagram

/-!
# Pivot atoms in the actual Folkman Boolean-ring amalgam

Choose one atom in each nonempty base fibre on both source sides.
These choices define three evaluation retractions from the actual
atom-grid-plus-private-point amalgam: to the B-side, C-side and base.

The pivot membership laws below establish the two same-side retractions.
The cross-base identities and bilinear extension are separate steps.
Empty base sorts and private outside atoms are included.
-/

namespace SuccessorTree.NonPrecompact

/-- Distinguished atoms of the two source rings over each base atom. -/
structure FolkmanAtomPivotChoices
    {A B C : Type*}
    (f : B → Option A) (g : C → Option A) where
  b : A → B
  c : A → C
  hb : ∀ a, f (b a) = some a
  hc : ∀ a, g (c a) = some a

/-- Nonempty fibres supply a pivot choice. -/
noncomputable def folkmanChooseAtomPivots
    {A B C : Type*}
    (f : B → Option A) (g : C → Option A)
    (hf : ∀ a : A, ∃ b : B, f b = some a)
    (hg : ∀ a : A, ∃ c : C, g c = some a) :
    FolkmanAtomPivotChoices f g where
  b := fun a => Classical.choose (hf a)
  c := fun a => Classical.choose (hg a)
  hb := fun a => Classical.choose_spec (hf a)
  hc := fun a => Classical.choose_spec (hg a)

/-- A selected amalgam atom in the image of source B-atom b.
Outside source atoms use their private points. -/
noncomputable def folkmanLeftPivot
    {A B C : Type*}
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g) (b : B) :
    FolkmanAtomAmalgam f g :=
  match h : f b with
  | none => .inr (.inl ⟨b, h⟩)
  | some a => .inl ⟨(b, P.c a), ⟨a, h, P.hc a⟩⟩

/-- The symmetric pivot for a source C-atom. -/
noncomputable def folkmanRightPivot
    {A B C : Type*}
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g) (c : C) :
    FolkmanAtomAmalgam f g :=
  match h : g c with
  | none => .inr (.inr ⟨c, h⟩)
  | some a => .inl ⟨(P.b a, c), ⟨a, P.hb a, h⟩⟩

/-- One grid atom selected above each common base atom. -/
noncomputable def folkmanBasePivot
    {A B C : Type*}
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g) (a : A) :
    FolkmanAtomAmalgam f g :=
  .inl ⟨(P.b a, P.c a), ⟨a, P.hb a, P.hc a⟩⟩

/-- Membership in a left image is detected by the selected pivot,
including on private outside atoms. -/
theorem folkmanLeftPivot_mem_leftMap
    {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s : Finset B) (b : B) :
    folkmanLeftPivot f g P b ∈ folkmanFinsetLeftMap f g s ↔ b ∈ s := by
  classical
  rw [folkmanFinsetLeftMap_mem]
  unfold folkmanLeftPivot
  split <;> simp [folkmanLeftImage]

/-- Membership in a right image is detected by its selected pivot. -/
theorem folkmanRightPivot_mem_rightMap
    {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s : Finset C) (c : C) :
    folkmanRightPivot f g P c ∈ folkmanFinsetRightMap f g s ↔ c ∈ s := by
  classical
  rw [folkmanFinsetRightMap_mem]
  unfold folkmanRightPivot
  split <;> simp [folkmanRightImage]

/-- The base pivot reads the selected B-atom. -/
theorem folkmanBasePivot_mem_leftMap
    {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s : Finset B) (a : A) :
    folkmanBasePivot f g P a ∈ folkmanFinsetLeftMap f g s ↔
      P.b a ∈ s := by
  classical
  simp [folkmanBasePivot, folkmanLeftImage]

/-- The base pivot reads the selected C-atom. -/
theorem folkmanBasePivot_mem_rightMap
    {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s : Finset C) (a : A) :
    folkmanBasePivot f g P a ∈ folkmanFinsetRightMap f g s ↔
      P.c a ∈ s := by
  classical
  simp [folkmanBasePivot, folkmanRightImage]

/-- Evaluate an amalgam element at all B-side pivots. -/
noncomputable def folkmanPivotLeftRetract
    {A B C : Type*}
    [Fintype B]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s : Finset (FolkmanAtomAmalgam f g)) : Finset B := by
  classical
  exact Finset.univ.filter (fun b => folkmanLeftPivot f g P b ∈ s)

/-- Evaluate an amalgam element at all C-side pivots. -/
noncomputable def folkmanPivotRightRetract
    {A B C : Type*}
    [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s : Finset (FolkmanAtomAmalgam f g)) : Finset C := by
  classical
  exact Finset.univ.filter (fun c => folkmanRightPivot f g P c ∈ s)

/-- Evaluate an amalgam element at the base grid pivots. -/
noncomputable def folkmanPivotBaseRetract
    {A B C : Type*}
    [Fintype A]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s : Finset (FolkmanAtomAmalgam f g)) : Finset A := by
  classical
  exact Finset.univ.filter (fun a => folkmanBasePivot f g P a ∈ s)

/-- The B-side retraction is a literal left inverse to the ring embedding. -/
theorem folkmanPivotLeftRetract_leftMap
    {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s : Finset B) :
    folkmanPivotLeftRetract f g P (folkmanFinsetLeftMap f g s) = s := by
  classical
  ext b
  simp only [folkmanPivotLeftRetract, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact folkmanLeftPivot_mem_leftMap f g P s b

/-- The C-side retraction is a literal left inverse to its embedding. -/
theorem folkmanPivotRightRetract_rightMap
    {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s : Finset C) :
    folkmanPivotRightRetract f g P (folkmanFinsetRightMap f g s) = s := by
  classical
  ext c
  simp only [folkmanPivotRightRetract, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact folkmanRightPivot_mem_rightMap f g P s c

end SuccessorTree.NonPrecompact
