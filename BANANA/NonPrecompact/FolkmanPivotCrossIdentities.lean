import BANANA.NonPrecompact.FolkmanAtomPivots

/-!
# Additivity and cross-base identities for actual Folkman pivot retractions

Each finite-subset pivot retraction is the inverse image of a
particular map of atom sets. Such inverse-image maps preserve the
additive Boolean-ring operation (symmetric difference).

The two cross identities say that evaluating an embedded source
subset at the opposite pivots depends only on the common base.
Together with the same-side identities proved in FolkmanAtomPivots,
these provide the hypotheses of the explicit pairing extension.

The pivot maps are linear for symmetric difference; they are not
asserted to preserve intersections or ring units.
-/

namespace SuccessorTree.NonPrecompact

/-- The left pivot retraction is additive over symmetric difference. -/
theorem folkmanPivotLeftRetract_symmDiff
    {A B C : Type*} [Fintype B]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s t : Finset (FolkmanAtomAmalgam f g)) :
    folkmanPivotLeftRetract f g P (symmDiff s t) =
      symmDiff (folkmanPivotLeftRetract f g P s)
        (folkmanPivotLeftRetract f g P t) := by
  classical
  ext b
  simp [folkmanPivotLeftRetract, Finset.mem_symmDiff]

/-- The right pivot retraction is additive over symmetric difference. -/
theorem folkmanPivotRightRetract_symmDiff
    {A B C : Type*} [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s t : Finset (FolkmanAtomAmalgam f g)) :
    folkmanPivotRightRetract f g P (symmDiff s t) =
      symmDiff (folkmanPivotRightRetract f g P s)
        (folkmanPivotRightRetract f g P t) := by
  classical
  ext c
  simp [folkmanPivotRightRetract, Finset.mem_symmDiff]

/-- The base pivot retraction is additive over symmetric difference. -/
theorem folkmanPivotBaseRetract_symmDiff
    {A B C : Type*} [Fintype A]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s t : Finset (FolkmanAtomAmalgam f g)) :
    folkmanPivotBaseRetract f g P (symmDiff s t) =
      symmDiff (folkmanPivotBaseRetract f g P s)
        (folkmanPivotBaseRetract f g P t) := by
  classical
  ext a
  simp [folkmanPivotBaseRetract, Finset.mem_symmDiff]

/-- The opposite pivot reads a B-subset only through the selected
B-representative of its C-base fibre; C-private atoms contribute zero. -/
theorem folkmanRightPivot_mem_leftMap_iff
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s : Finset B) (c : C) :
    folkmanRightPivot f g P c ∈ folkmanFinsetLeftMap f g s ↔
      ∃ a : A, g c = some a ∧ P.b a ∈ s := by
  classical
  rw [folkmanFinsetLeftMap_mem]
  unfold folkmanRightPivot
  split <;> simp_all [folkmanLeftImage]

/-- The symmetric opposite-pivot membership equivalence. -/
theorem folkmanLeftPivot_mem_rightMap_iff
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s : Finset C) (b : B) :
    folkmanLeftPivot f g P b ∈ folkmanFinsetRightMap f g s ↔
      ∃ a : A, f b = some a ∧ P.c a ∈ s := by
  classical
  rw [folkmanFinsetRightMap_mem]
  unfold folkmanLeftPivot
  split <;> simp_all [folkmanRightImage]

/-- The base retraction of an embedded B-subset is decided by
the distinguished atom of each B-base fibre. -/
theorem folkmanPivotBaseRetract_leftMap_mem
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s : Finset B) (a : A) :
    a ∈ folkmanPivotBaseRetract f g P (folkmanFinsetLeftMap f g s) ↔
      P.b a ∈ s := by
  classical
  simpa [folkmanPivotBaseRetract] using
    (folkmanBasePivot_mem_leftMap f g P s a)

/-- The corresponding base-retraction description for a C-subset. -/
theorem folkmanPivotBaseRetract_rightMap_mem
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g)
    (s : Finset C) (a : A) :
    a ∈ folkmanPivotBaseRetract f g P (folkmanFinsetRightMap f g s) ↔
      P.c a ∈ s := by
  classical
  simpa [folkmanPivotBaseRetract] using
    (folkmanBasePivot_mem_rightMap f g P s a)

/-- Evaluating B's embedded ring at C's pivots agrees with
the C-base embedding of the base-pivot evaluation. -/
theorem folkmanPivotRightRetract_leftMap
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g) (s : Finset B) :
    folkmanPivotRightRetract f g P (folkmanFinsetLeftMap f g s) =
      folkmanFinsetBaseRight g
        (folkmanPivotBaseRetract f g P (folkmanFinsetLeftMap f g s)) := by
  classical
  ext c
  calc
    c ∈ folkmanPivotRightRetract f g P (folkmanFinsetLeftMap f g s) ↔
        ∃ a : A, g c = some a ∧ P.b a ∈ s := by
      simpa [folkmanPivotRightRetract] using
        (folkmanRightPivot_mem_leftMap_iff f g P s c)
    _ ↔ c ∈ folkmanFinsetBaseRight g
          (folkmanPivotBaseRetract f g P
            (folkmanFinsetLeftMap f g s)) := by
      rw [folkmanFinsetBaseRight_mem]
      constructor
      · rintro ⟨a, hc, hs⟩
        exact ⟨a, (folkmanPivotBaseRetract_leftMap_mem f g P s a).2 hs, hc⟩
      · rintro ⟨a, ha, hc⟩
        exact ⟨a, hc, (folkmanPivotBaseRetract_leftMap_mem f g P s a).1 ha⟩

/-- Evaluating C's embedded ring at B's pivots agrees with
the B-base embedding of the base-pivot evaluation. -/
theorem folkmanPivotLeftRetract_rightMap
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (P : FolkmanAtomPivotChoices f g) (s : Finset C) :
    folkmanPivotLeftRetract f g P (folkmanFinsetRightMap f g s) =
      folkmanFinsetBaseLeft f
        (folkmanPivotBaseRetract f g P (folkmanFinsetRightMap f g s)) := by
  classical
  ext b
  calc
    b ∈ folkmanPivotLeftRetract f g P (folkmanFinsetRightMap f g s) ↔
        ∃ a : A, f b = some a ∧ P.c a ∈ s := by
      simpa [folkmanPivotLeftRetract] using
        (folkmanLeftPivot_mem_rightMap_iff f g P s b)
    _ ↔ b ∈ folkmanFinsetBaseLeft f
          (folkmanPivotBaseRetract f g P
            (folkmanFinsetRightMap f g s)) := by
      rw [folkmanFinsetBaseLeft_mem]
      constructor
      · rintro ⟨a, hb, hs⟩
        exact ⟨a, (folkmanPivotBaseRetract_rightMap_mem f g P s a).2 hs, hb⟩
      · rintro ⟨a, ha, hb⟩
        exact ⟨a, hb, (folkmanPivotBaseRetract_rightMap_mem f g P s a).1 ha⟩

end SuccessorTree.NonPrecompact
