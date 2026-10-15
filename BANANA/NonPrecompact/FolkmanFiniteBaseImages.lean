import BANANA.NonPrecompact.FolkmanFiniteBooleanRingMaps

/-!
# Exact common-base image for the finite Folkman Boolean-ring amalgam

The finite atom-grid-plus-private-point embeddings preserve Boolean-ring
operations. Here the common base is realised by inverse images of selected
base atoms under the two partial atom maps, and this is exactly the
intersection of the two image Boolean rings.

This checks the full finite **sortwise** strong-intersection diagram.
It does not package the two sorts together with their bilinear pairing.
-/

namespace SuccessorTree.NonPrecompact

/-- The image of a selected subset of base atoms in the left atom set. -/
noncomputable def folkmanFinsetBaseLeft
    {A B : Type*} [Fintype B]
    (f : B → Option A) (SA : Finset A) : Finset B := by
  classical
  exact Finset.univ.filter (fun b => ∃ a ∈ SA, f b = some a)

/-- The corresponding base image in the right atom set. -/
noncomputable def folkmanFinsetBaseRight
    {A C : Type*} [Fintype C]
    (g : C → Option A) (SA : Finset A) : Finset C := by
  classical
  exact Finset.univ.filter (fun c => ∃ a ∈ SA, g c = some a)

@[simp] theorem folkmanFinsetBaseLeft_mem
    {A B : Type*} [Fintype B]
    (f : B → Option A) (SA : Finset A) (b : B) :
    b ∈ folkmanFinsetBaseLeft f SA ↔ ∃ a ∈ SA, f b = some a := by
  classical
  simp [folkmanFinsetBaseLeft]

@[simp] theorem folkmanFinsetBaseRight_mem
    {A C : Type*} [Fintype C]
    (g : C → Option A) (SA : Finset A) (c : C) :
    c ∈ folkmanFinsetBaseRight g SA ↔ ∃ a ∈ SA, g c = some a := by
  classical
  simp [folkmanFinsetBaseRight]

/-- The two embeddings agree on all elements of the common base,
including the zero element and the non-unital setting. -/
theorem folkmanFinsetBase_commutes
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A) (SA : Finset A) :
    folkmanFinsetLeftMap f g (folkmanFinsetBaseLeft f SA) =
      folkmanFinsetRightMap f g (folkmanFinsetBaseRight g SA) := by
  classical
  ext p
  simp only [folkmanFinsetLeftMap_mem, folkmanFinsetRightMap_mem]
  cases p with
  | inl p =>
      rcases p with ⟨⟨b, c⟩, ⟨a, hb, hc⟩⟩
      simp [folkmanLeftImage, folkmanRightImage, hb, hc]
  | inr p =>
      cases p with
      | inl b =>
          simp [folkmanLeftImage, folkmanRightImage, b.property]
      | inr c =>
          simp [folkmanLeftImage, folkmanRightImage, c.property]

/-- Any equality of left and right finite atom-ring images comes
from one and the same finite subset of base atoms. -/
theorem folkmanFinsetImages_common_base
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (hf : ∀ a : A, ∃ b : B, f b = some a)
    (hg : ∀ a : A, ∃ c : C, g c = some a)
    (SB : Finset B) (SC : Finset C)
    (heq : folkmanFinsetLeftMap f g SB =
      folkmanFinsetRightMap f g SC) :
    ∃ SA : Finset A,
      SB = folkmanFinsetBaseLeft f SA ∧
      SC = folkmanFinsetBaseRight g SA := by
  classical
  obtain ⟨SA, hleft, houtsideL, hright, houtsideR⟩ :=
    folkmanFinsetImages_strong_intersection f g hf hg SB SC heq
  let T : Finset A := Finset.univ.filter (fun a => a ∈ SA)
  refine ⟨T, ?_, ?_⟩
  · ext b
    cases h : f b with
    | none =>
        have hn : b ∉ SB := houtsideL b h
        simp [hn, h]
    | some a =>
        calc
          b ∈ SB ↔ a ∈ SA := hleft b a h
          _ ↔ b ∈ folkmanFinsetBaseLeft f T := by
            simp [T, h]
  · ext c
    cases h : g c with
    | none =>
        have hn : c ∉ SC := houtsideR c h
        simp [hn, h]
    | some a =>
        calc
          c ∈ SC ↔ a ∈ SA := hright c a h
          _ ↔ c ∈ folkmanFinsetBaseRight g T := by
            simp [T, h]

/-- The complete finite sortwise strong-amalgamation characterisation:
the left and right Boolean-ring images meet exactly in the common-base
image, not merely in a set-theoretic subset. -/
theorem folkmanFinsetImages_eq_iff_common_base
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (f : B → Option A) (g : C → Option A)
    (hf : ∀ a : A, ∃ b : B, f b = some a)
    (hg : ∀ a : A, ∃ c : C, g c = some a)
    (SB : Finset B) (SC : Finset C) :
    folkmanFinsetLeftMap f g SB =
      folkmanFinsetRightMap f g SC ↔
    ∃ SA : Finset A,
      SB = folkmanFinsetBaseLeft f SA ∧
      SC = folkmanFinsetBaseRight g SA := by
  constructor
  · exact folkmanFinsetImages_common_base f g hf hg SB SC
  · rintro ⟨SA, rfl, rfl⟩
    exact folkmanFinsetBase_commutes f g SA

end SuccessorTree.NonPrecompact
