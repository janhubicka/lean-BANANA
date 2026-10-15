import BANANA.NonPrecompact.FolkmanFiniteBaseImages

/-!
# Both Boolean-ring sorts in the finite Folkman atom amalgam

The circulation proof first amalgamates the two non-unital Boolean-ring
sorts by compatible atom-fibre grids and distinct private points.  This
file packages those two constructions into one *two-sorted ring diagram*.

Every embedding here is injective; both copies of the base commute in
the amalgam, and their images intersect exactly in the common base.
The bilinear pairing between the sorts is NOT yet supplied.  The
two-sorted Fraïssé amalgamation theorem therefore remains separate.
-/

namespace SuccessorTree.NonPrecompact

/-- Finite atom data on both sorts of a Folkman--BANANA amalgamation
diagram.  The nonempty fibre hypotheses come from injectivity of the
base embeddings and must not be omitted. -/
structure FolkmanFiniteTwoSortAtomDiagram
    (AL BL CL AR BR CR : Type*)
    [Fintype AL] [Fintype BL] [Fintype CL]
    [Fintype AR] [Fintype BR] [Fintype CR] where
  fL : BL → Option AL
  gL : CL → Option AL
  fR : BR → Option AR
  gR : CR → Option AR
  hfL : ∀ a : AL, ∃ b : BL, fL b = some a
  hgL : ∀ a : AL, ∃ c : CL, gL c = some a
  hfR : ∀ a : AR, ∃ b : BR, fR b = some a
  hgR : ∀ a : AR, ∃ c : CR, gR c = some a


/-- Addition on a pair of finite Boolean-ring atom supports; the sorts
remain distinct, with symmetric difference on each coordinate. -/
noncomputable def folkmanTwoSortSymmDiff
    {X Y : Type*} (x y : Finset X × Finset Y) :
    Finset X × Finset Y := by
  classical
  exact (symmDiff x.1 y.1, symmDiff x.2 y.2)

/-- Multiplication on a pair of finite atom supports. -/
noncomputable def folkmanTwoSortInter
    {X Y : Type*} (x y : Finset X × Finset Y) :
    Finset X × Finset Y := by
  classical
  exact (x.1 ∩ y.1, x.2 ∩ y.2)

namespace FolkmanFiniteTwoSortAtomDiagram

variable {AL BL CL AR BR CR : Type*}
variable [Fintype AL] [Fintype BL] [Fintype CL]
variable [Fintype AR] [Fintype BR] [Fintype CR]
variable (D : FolkmanFiniteTwoSortAtomDiagram AL BL CL AR BR CR)

/-- Embedding of both base ring sorts into the B-side rings. -/
noncomputable def baseB
    (a : Finset AL × Finset AR) : Finset BL × Finset BR :=
  (folkmanFinsetBaseLeft D.fL a.1,
   folkmanFinsetBaseLeft D.fR a.2)

/-- Embedding of both base ring sorts into the C-side rings. -/
noncomputable def baseC
    (a : Finset AL × Finset AR) : Finset CL × Finset CR :=
  (folkmanFinsetBaseRight D.gL a.1,
   folkmanFinsetBaseRight D.gR a.2)

/-- B-side embedding into the two powerset rings of the atom-grid
amalgam, keeping the sorts separate. -/
noncomputable def embedB
    (b : Finset BL × Finset BR) :
    Finset (FolkmanAtomAmalgam D.fL D.gL) ×
      Finset (FolkmanAtomAmalgam D.fR D.gR) :=
  (folkmanFinsetLeftMap D.fL D.gL b.1,
   folkmanFinsetLeftMap D.fR D.gR b.2)

/-- C-side embedding into the same pair of amalgam rings. -/
noncomputable def embedC
    (c : Finset CL × Finset CR) :
    Finset (FolkmanAtomAmalgam D.fL D.gL) ×
      Finset (FolkmanAtomAmalgam D.fR D.gR) :=
  (folkmanFinsetRightMap D.fL D.gL c.1,
   folkmanFinsetRightMap D.fR D.gR c.2)

/-- Both Boolean-ring embeddings on the B side are injective. -/
theorem embedB_injective : Function.Injective D.embedB := by
  intro b b' h
  apply Prod.ext
  · exact (folkmanFinsetLeftMap_injective D.fL D.gL D.hgL)
      (congrArg Prod.fst h)
  · exact (folkmanFinsetLeftMap_injective D.fR D.gR D.hgR)
      (congrArg Prod.snd h)

/-- Both Boolean-ring embeddings on the C side are injective. -/
theorem embedC_injective : Function.Injective D.embedC := by
  intro c c' h
  apply Prod.ext
  · exact (folkmanFinsetRightMap_injective D.fL D.gL D.hfL)
      (congrArg Prod.fst h)
  · exact (folkmanFinsetRightMap_injective D.fR D.gR D.hfR)
      (congrArg Prod.snd h)


/-- The B-side map preserves zero in both Boolean-ring sorts. -/
theorem embedB_zero :
    D.embedB (∅, ∅) = (∅, ∅) := by
  apply Prod.ext
  · exact folkmanFinsetLeftMap_empty D.fL D.gL
  · exact folkmanFinsetLeftMap_empty D.fR D.gR

/-- The C-side map preserves zero in both sorts. -/
theorem embedC_zero :
    D.embedC (∅, ∅) = (∅, ∅) := by
  apply Prod.ext
  · exact folkmanFinsetRightMap_empty D.fL D.gL
  · exact folkmanFinsetRightMap_empty D.fR D.gR

/-- The B-side embeddings preserve Boolean-ring addition. -/
theorem embedB_symmDiff
    (x y : Finset BL × Finset BR) :
    D.embedB (folkmanTwoSortSymmDiff x y) =
      folkmanTwoSortSymmDiff (D.embedB x) (D.embedB y) := by
  classical
  apply Prod.ext
  · ext z
    have hz := congrArg (fun t => z ∈ t) (folkmanFinsetLeftMap_symmDiff D.fL D.gL x.1 y.1)
    simp only [embedB, folkmanTwoSortSymmDiff, Prod.fst, Finset.mem_symmDiff]
    rw [hz] <;> simp only [Finset.mem_symmDiff]
  · ext z
    have hz := congrArg (fun t => z ∈ t) (folkmanFinsetLeftMap_symmDiff D.fR D.gR x.2 y.2)
    simp only [embedB, folkmanTwoSortSymmDiff, Prod.snd, Finset.mem_symmDiff]
    rw [hz] <;> simp only [Finset.mem_symmDiff]

/-- The C-side embeddings preserve Boolean-ring addition. -/
theorem embedC_symmDiff
    (x y : Finset CL × Finset CR) :
    D.embedC (folkmanTwoSortSymmDiff x y) =
      folkmanTwoSortSymmDiff (D.embedC x) (D.embedC y) := by
  classical
  apply Prod.ext
  · ext z
    have hz := congrArg (fun t => z ∈ t) (folkmanFinsetRightMap_symmDiff D.fL D.gL x.1 y.1)
    simp only [embedC, folkmanTwoSortSymmDiff, Prod.fst, Finset.mem_symmDiff]
    rw [hz] <;> simp only [Finset.mem_symmDiff]
  · ext z
    have hz := congrArg (fun t => z ∈ t) (folkmanFinsetRightMap_symmDiff D.fR D.gR x.2 y.2)
    simp only [embedC, folkmanTwoSortSymmDiff, Prod.snd, Finset.mem_symmDiff]
    rw [hz] <;> simp only [Finset.mem_symmDiff]

/-- The B-side embeddings preserve Boolean-ring multiplication. -/
theorem embedB_inter
    (x y : Finset BL × Finset BR) :
    D.embedB (folkmanTwoSortInter x y) =
      folkmanTwoSortInter (D.embedB x) (D.embedB y) := by
  classical
  apply Prod.ext
  · ext z
    have hz := congrArg (fun t => z ∈ t) (folkmanFinsetLeftMap_inter D.fL D.gL x.1 y.1)
    simp only [embedB, folkmanTwoSortInter, Prod.fst, Finset.mem_inter]
    rw [hz] <;> simp only [Finset.mem_inter]
  · ext z
    have hz := congrArg (fun t => z ∈ t) (folkmanFinsetLeftMap_inter D.fR D.gR x.2 y.2)
    simp only [embedB, folkmanTwoSortInter, Prod.snd, Finset.mem_inter]
    rw [hz] <;> simp only [Finset.mem_inter]

/-- The C-side embeddings preserve Boolean-ring multiplication. -/
theorem embedC_inter
    (x y : Finset CL × Finset CR) :
    D.embedC (folkmanTwoSortInter x y) =
      folkmanTwoSortInter (D.embedC x) (D.embedC y) := by
  classical
  apply Prod.ext
  · ext z
    have hz := congrArg (fun t => z ∈ t) (folkmanFinsetRightMap_inter D.fL D.gL x.1 y.1)
    simp only [embedC, folkmanTwoSortInter, Prod.fst, Finset.mem_inter]
    rw [hz] <;> simp only [Finset.mem_inter]
  · ext z
    have hz := congrArg (fun t => z ∈ t) (folkmanFinsetRightMap_inter D.fR D.gR x.2 y.2)
    simp only [embedC, folkmanTwoSortInter, Prod.snd, Finset.mem_inter]
    rw [hz] <;> simp only [Finset.mem_inter]

/-- The two finite ring-sort embeddings agree on their common base. -/
theorem base_commutes (a : Finset AL × Finset AR) :
    D.embedB (D.baseB a) = D.embedC (D.baseC a) := by
  apply Prod.ext
  · exact folkmanFinsetBase_commutes D.fL D.gL a.1
  · exact folkmanFinsetBase_commutes D.fR D.gR a.2

/-- The *two-sorted ring* images meet precisely in the image of the
same base ring pair. This does not yet concern the bilinear pairing. -/
theorem images_eq_iff_common_base
    (b : Finset BL × Finset BR)
    (c : Finset CL × Finset CR) :
    D.embedB b = D.embedC c ↔
      ∃ a : Finset AL × Finset AR,
        b = D.baseB a ∧ c = D.baseC a := by
  constructor
  · intro h
    have hL :
        folkmanFinsetLeftMap D.fL D.gL b.1 =
          folkmanFinsetRightMap D.fL D.gL c.1 :=
      congrArg Prod.fst h
    have hR :
        folkmanFinsetLeftMap D.fR D.gR b.2 =
          folkmanFinsetRightMap D.fR D.gR c.2 :=
      congrArg Prod.snd h
    obtain ⟨aL, hbL, hcL⟩ :=
      (folkmanFinsetImages_eq_iff_common_base
        D.fL D.gL D.hfL D.hgL b.1 c.1).mp hL
    obtain ⟨aR, hbR, hcR⟩ :=
      (folkmanFinsetImages_eq_iff_common_base
        D.fR D.gR D.hfR D.hgR b.2 c.2).mp hR
    exact ⟨(aL, aR), Prod.ext hbL hbR, Prod.ext hcL hcR⟩
  · rintro ⟨a, rfl, rfl⟩
    exact D.base_commutes a

end FolkmanFiniteTwoSortAtomDiagram
end SuccessorTree.NonPrecompact
