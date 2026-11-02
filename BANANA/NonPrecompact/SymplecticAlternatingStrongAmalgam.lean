import BANANA.NonPrecompact.SymplecticAmalgam

/-!
# Strong coordinate amalgamation of finite alternating binary forms

The circulation's symplectic application needs the hereditary class of
ALL finite alternating bilinear forms, including degenerate forms and
one-dimensional zero forms. The class of nondegenerate finite forms is
not hereditary and contains no one-dimensional forms.

Existing SymplecticAmalgam proves the zero-cross block matrix identities.
This module adds the corresponding LINEAR maps on vector coordinates,
their injectivity and their exact intersection, then packages those
results with preservation of alternation and of both old matrices.

An alternating form over F₂ has a matrix with zero diagonal AND
symmetry; the latter follows from alternation of the bilinear form,
not from a zero diagonal matrix by itself. Both are explicit below.

The theorem handles a diagram already expressed in shared bases.
Moving arbitrary injective isometries into these coordinates is a
separate basis-choice step. A kernel build is required before claiming
the new Lean declarations verified.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Include the left source space in the common basis-coordinate
space, extending by zero on the private right complement. -/
def symplecticBlockVectorLeft {A X Y : Type*} :
    (Sum A X → F2) →ₗ[F2] (Sum A (Sum X Y) → F2) where
  toFun := fun u k =>
    match k with
    | .inl a => u (.inl a)
    | .inr (.inl x) => u (.inr x)
    | .inr (.inr _) => 0
  map_add' u v := by
    funext k
    cases k with
    | inl a => simp [Pi.add_apply]
    | inr t =>
        cases t with
        | inl x => simp [Pi.add_apply]
        | inr y => simp [Pi.add_apply]
  map_smul' c u := by
    funext k
    cases k with
    | inl a => simp [Pi.smul_apply]
    | inr t =>
        cases t with
        | inl x => simp [Pi.smul_apply]
        | inr y => simp [Pi.smul_apply]

/-- Include the right source space, extending by zero on the private
left complement. -/
def symplecticBlockVectorRight {A X Y : Type*} :
    (Sum A Y → F2) →ₗ[F2] (Sum A (Sum X Y) → F2) where
  toFun := fun v k =>
    match k with
    | .inl a => v (.inl a)
    | .inr (.inl _) => 0
    | .inr (.inr y) => v (.inr y)
  map_add' u v := by
    funext k
    cases k with
    | inl a => simp [Pi.add_apply]
    | inr t =>
        cases t with
        | inl x => simp [Pi.add_apply]
        | inr y => simp [Pi.add_apply]
  map_smul' c u := by
    funext k
    cases k with
    | inl a => simp [Pi.smul_apply]
    | inr t =>
        cases t with
        | inl x => simp [Pi.smul_apply]
        | inr y => simp [Pi.smul_apply]

/-- Both vector-space inclusion maps are injective, even when any
one of the three summands is empty. -/
theorem symplecticBlockVectorLeft_injective {A X Y : Type*} :
    Function.Injective (symplecticBlockVectorLeft (A := A) (X := X) (Y := Y)) := by
  intro u v h
  funext k
  cases k with
  | inl a =>
      simpa [symplecticBlockVectorLeft] using congrFun h (.inl a)
  | inr x =>
      simpa [symplecticBlockVectorLeft] using congrFun h (.inr (.inl x))

theorem symplecticBlockVectorRight_injective {A X Y : Type*} :
    Function.Injective (symplecticBlockVectorRight (A := A) (X := X) (Y := Y)) := by
  intro u v h
  funext k
  cases k with
  | inl a =>
      simpa [symplecticBlockVectorRight] using congrFun h (.inl a)
  | inr y =>
      simpa [symplecticBlockVectorRight] using congrFun h (.inr (.inr y))

/-- The common source A inside the left coordinate space. -/
def symplecticBlockVectorCommonLeft {A X : Type*}
    (w : A → F2) : Sum A X → F2
  | .inl a => w a
  | .inr _ => 0

/-- The common source A inside the right coordinate space. -/
def symplecticBlockVectorCommonRight {A Y : Type*}
    (w : A → F2) : Sum A Y → F2
  | .inl a => w a
  | .inr _ => 0

/-- Exact STRONG image intersection on complete vector spaces,
not merely on basis indices. There is no unwanted identification
between either private complement and the other source. -/
theorem symplecticBlockVector_intersection
    {A X Y : Type*}
    (u : Sum A X → F2)
    (v : Sum A Y → F2) :
    symplecticBlockVectorLeft u = symplecticBlockVectorRight v ↔
      ∃ w : A → F2,
        u = symplecticBlockVectorCommonLeft w ∧
        v = symplecticBlockVectorCommonRight w := by
  constructor
  · intro h
    refine ⟨fun a => u (.inl a), ?_, ?_⟩
    · funext k
      cases k with
      | inl a => rfl
      | inr x =>
          have hx := congrFun h (.inr (.inl x))
          simpa [symplecticBlockVectorLeft,
            symplecticBlockVectorRight,
            symplecticBlockVectorCommonLeft] using hx
    · funext k
      cases k with
      | inl a =>
          have ha := congrFun h (.inl a)
          simpa [symplecticBlockVectorLeft,
            symplecticBlockVectorRight,
            symplecticBlockVectorCommonRight] using ha.symm
      | inr y =>
          have hy := congrFun h (.inr (.inr y))
          simpa [symplecticBlockVectorLeft,
            symplecticBlockVectorRight,
            symplecticBlockVectorCommonRight] using hy.symm
  · rintro ⟨w, rfl, rfl⟩
    funext k
    cases k with
    | inl a => rfl
    | inr z =>
        cases z <;> rfl

/-- In any chosen bases with a shared A-block, two finite alternating
F₂ matrices have a common alternating extension whose coordinate
inclusions are injective and meet EXACTLY in the shared A-space.

No nondegeneracy, parity-of-dimension or nonempty-sort hypothesis.
This is the finite block diagram; the arbitrary-embedding reduction
by choice of complementary bases remains separate. -/
theorem symplecticAlternatingBlock_exists_strongAmalgam
    {A X Y : Type*}
    (B : Matrix (Sum A X) (Sum A X) F2)
    (C : Matrix (Sum A Y) (Sum A Y) F2)
    (hcommon : ∀ a a',
      B (.inl a) (.inl a') = C (.inl a) (.inl a'))
    (hBdiag : ∀ i, B i i = 0)
    (hCdiag : ∀ i, C i i = 0)
    (hBsymm : ∀ i j, B i j = B j i)
    (hCsymm : ∀ i j, C i j = C j i) :
    ∃ D : Matrix (Sum A (Sum X Y)) (Sum A (Sum X Y)) F2,
      D.submatrix
          (symplecticAmalgamLeft : Sum A X → Sum A (Sum X Y))
          (symplecticAmalgamLeft : Sum A X → Sum A (Sum X Y)) = B ∧
      D.submatrix
          (symplecticAmalgamRight : Sum A Y → Sum A (Sum X Y))
          (symplecticAmalgamRight : Sum A Y → Sum A (Sum X Y)) = C ∧
      (∀ i, D i i = 0) ∧
      (∀ i j, D i j = D j i) ∧
      Function.Injective (symplecticBlockVectorLeft (A := A) (X := X) (Y := Y)) ∧
      Function.Injective (symplecticBlockVectorRight (A := A) (X := X) (Y := Y)) ∧
      (∀ (u : Sum A X → F2) (v : Sum A Y → F2),
        symplecticBlockVectorLeft u = symplecticBlockVectorRight v ↔
          ∃ w : A → F2,
            u = symplecticBlockVectorCommonLeft w ∧
            v = symplecticBlockVectorCommonRight w) := by
  refine ⟨symplecticBlockAmalgam B C,
    symplecticBlockAmalgam_left B C,
    symplecticBlockAmalgam_right B C hcommon,
    symplecticBlockAmalgam_diag_zero B C hBdiag hCdiag,
    symplecticBlockAmalgam_symmetric B C hBsymm hCsymm,
    symplecticBlockVectorLeft_injective,
    symplecticBlockVectorRight_injective, ?_⟩
  intro u v
  exact symplecticBlockVector_intersection u v

end SuccessorTree.NonPrecompact
