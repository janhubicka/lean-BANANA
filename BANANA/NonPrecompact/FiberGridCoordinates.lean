import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Defs

/-!
# Generic compatible-atom grid coordinates

The fibre-product geometry and exact subset intersection do not use parity
or colouring. They are extracted verbatim from the original
`FiberProductStrong` and `FiberProductParityAmalgam` modules.
-/

namespace SuccessorTree.NonPrecompact

/-- Compatible pairs for a cospan of maps. -/
abbrev CompatiblePair
    {A B C : Type*}
    (f : B → A) (g : C → A) :=
  {p : B × C // f p.1 = g p.2}

/-- First projection from a fibre product. -/
def compatiblePairFst
    {A B C : Type*}
    {f : B → A} {g : C → A} :
    CompatiblePair f g → B :=
  fun p => p.1.1

/-- Second projection from a fibre product. -/
def compatiblePairSnd
    {A B C : Type*}
    {f : B → A} {g : C → A} :
    CompatiblePair f g → C :=
  fun p => p.1.2

theorem compatiblePairFst_surjective
    {A B C : Type*}
    (f : B → A) (g : C → A)
    (hg : Function.Surjective g) :
    Function.Surjective
      (compatiblePairFst (f := f) (g := g)) := by
  intro b
  obtain ⟨c, hc⟩ := hg (f b)
  refine ⟨⟨(b,c), ?_⟩, rfl⟩
  exact hc.symm

theorem compatiblePairSnd_surjective
    {A B C : Type*}
    (f : B → A) (g : C → A)
    (hf : Function.Surjective f) :
    Function.Surjective
      (compatiblePairSnd (f := f) (g := g)) := by
  intro c
  obtain ⟨b, hb⟩ := hf (g c)
  refine ⟨⟨(b,c), ?_⟩, rfl⟩
  exact hb

/-- Membership in a subset of B which agrees, on every compatible pair, with
membership in a subset of C is constant on every f-fibre. -/
theorem mem_constant_on_fiber_left
    {A B C : Type*}
    (f : B → A) (g : C → A)
    (hg : Function.Surjective g)
    (SB : Set B) (SC : Set C)
    (hcompat :
      ∀ p : CompatiblePair f g,
        p.1.1 ∈ SB ↔ p.1.2 ∈ SC)
    {b₁ b₂ : B} (hfb : f b₁ = f b₂) :
    b₁ ∈ SB ↔ b₂ ∈ SB := by
  obtain ⟨c, hc⟩ := hg (f b₁)
  let p₁ : CompatiblePair f g :=
    ⟨(b₁,c), hc.symm⟩
  let p₂ : CompatiblePair f g :=
    ⟨(b₂,c), by rw [← hfb]; exact hc.symm⟩
  exact (hcompat p₁).trans (hcompat p₂).symm

/-- The analogous constancy on g-fibres. -/
theorem mem_constant_on_fiber_right
    {A B C : Type*}
    (f : B → A) (g : C → A)
    (hf : Function.Surjective f)
    (SB : Set B) (SC : Set C)
    (hcompat :
      ∀ p : CompatiblePair f g,
        p.1.1 ∈ SB ↔ p.1.2 ∈ SC)
    {c₁ c₂ : C} (hgc : g c₁ = g c₂) :
    c₁ ∈ SC ↔ c₂ ∈ SC := by
  obtain ⟨b, hb⟩ := hf (g c₁)
  let p₁ : CompatiblePair f g :=
    ⟨(b,c₁), hb⟩
  let p₂ : CompatiblePair f g :=
    ⟨(b,c₂), by rw [← hgc]; exact hb⟩
  exact (hcompat p₁).symm.trans (hcompat p₂)

/-- Strong intersection for a fibre product: if a subset of the compatible
pairs is both the inverse image of SB under the B-projection and the inverse
image of SC under the C-projection, then SB and SC are inverse images of one
common subset of A. -/
theorem exists_common_subset_of_fiberProduct
    {A B C : Type*}
    (f : B → A) (g : C → A)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (SB : Set B) (SC : Set C)
    (hcompat :
      ∀ p : CompatiblePair f g,
        p.1.1 ∈ SB ↔ p.1.2 ∈ SC) :
    ∃ SA : Set A,
      (∀ b, b ∈ SB ↔ f b ∈ SA) ∧
      (∀ c, c ∈ SC ↔ g c ∈ SA) := by
  let SA : Set A := {a | ∃ b, f b = a ∧ b ∈ SB}
  refine ⟨SA, ?_, ?_⟩
  · intro b
    constructor
    · intro hb
      exact ⟨b, rfl, hb⟩
    · rintro ⟨b', hb', hb'S⟩
      exact
        (mem_constant_on_fiber_left
          f g hg SB SC hcompat hb'.symm).2 hb'S
  · intro c
    constructor
    · intro hc
      obtain ⟨b, hb⟩ := hf (g c)
      refine ⟨b, hb, ?_⟩
      let p : CompatiblePair f g := ⟨(b,c), hb⟩
      exact (hcompat p).2 hc
    · rintro ⟨b, hb, hbS⟩
      obtain ⟨c', hc'⟩ := hg (f b)
      have hc'eq : g c' = g c := by
        rw [hc', hb]
      let p : CompatiblePair f g := ⟨(b,c'), hc'.symm⟩
      have hc'S : c' ∈ SC := (hcompat p).1 hbS
      exact
        (mem_constant_on_fiber_right
          f g hf SB SC hcompat hc'eq).1 hc'S

/-- Left fibre over one base atom. -/
abbrev LeftFiber
    {A B : Type*} (f : B → A) (a : A) :=
  {b : B // f b = a}

/-- Right fibre over one base atom. -/
abbrev RightFiber
    {A C : Type*} (g : C → A) (a : A) :=
  {c : C // g c = a}

/-- Atom grid of the fibre-product amalgam, indexed by the common base atom. -/
abbrev FiberGrid
    {A B C : Type*} (f : B → A) (g : C → A) :=
  Σ a : A, LeftFiber f a × RightFiber g a

/-- A chosen row in every nonempty left fibre. -/
noncomputable def leftFiberBase
    {A B : Type*}
    (f : B → A) (hf : Function.Surjective f) (a : A) :
    LeftFiber f a :=
  ⟨Classical.choose (hf a), Classical.choose_spec (hf a)⟩

/-- A chosen column in every nonempty right fibre. -/
noncomputable def rightFiberBase
    {A C : Type*}
    (g : C → A) (hg : Function.Surjective g) (a : A) :
    RightFiber g a :=
  ⟨Classical.choose (hg a), Classical.choose_spec (hg a)⟩

/-- Forgetting the explicit base coordinate identifies the sigma-type atom
grid with the usual compatible-pair fibre product. -/
noncomputable def fiberGridEquivCompatiblePair
    {A B C : Type*}
    (f : B → A) (g : C → A) :
    FiberGrid f g ≃ CompatiblePair f g where
  toFun p :=
    ⟨(p.2.1.1, p.2.2.1),
      p.2.1.2.trans p.2.2.2.symm⟩
  invFun p :=
    ⟨f p.1.1,
      (⟨p.1.1, rfl⟩,
        ⟨p.1.2, p.2.symm⟩)⟩
  left_inv p := by
    rcases p with ⟨a, ⟨b, c⟩⟩
    rcases b with ⟨b, hb⟩
    rcases c with ⟨c, hc⟩
    subst a
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> rfl

/-- Strong intersection for the sigma-type atom grid.  If membership pulled
back from B agrees with membership pulled back from C on every grid atom,
then both subsets come from one common subset of A. -/
theorem exists_common_subset_of_fiberGrid
    {A B C : Type*}
    (f : B → A) (g : C → A)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (SB : Set B) (SC : Set C)
    (hcompat :
      ∀ p : FiberGrid f g,
        p.2.1.1 ∈ SB ↔ p.2.2.1 ∈ SC) :
    ∃ SA : Set A,
      (∀ b, b ∈ SB ↔ f b ∈ SA) ∧
      (∀ c, c ∈ SC ↔ g c ∈ SA) := by
  apply exists_common_subset_of_fiberProduct
    f g hf hg SB SC
  intro p
  let q := (fiberGridEquivCompatiblePair f g).symm p
  simpa [q, fiberGridEquivCompatiblePair] using hcompat q

end SuccessorTree.NonPrecompact
