import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Atoms

/-!
# Canonical finite Boolean-algebra coordinates and partitions

These generic declarations were extracted from the original finite
Boolean representation and powerset-embedding modules. They depend only
on Mathlib, so later mass and marking arguments can use the same
coordinates without importing unrelated colouring constructions.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Atoms of an arbitrary Boolean algebra, as a subtype. -/
abbrev PrebananaAbstractAtoms (α : Type*) [BooleanAlgebra α] :=
  {a : α // IsAtom a}

/-- An arbitrary finite Boolean algebra is order-isomorphic to
the set of subsets of its atoms. -/
noncomputable def prebananaFiniteBooleanAtomSetOrderIso
    (α : Type*) [BooleanAlgebra α] [Fintype α] :
    α ≃o Set (PrebananaAbstractAtoms α) := by
  letI : CompleteAtomicBooleanAlgebra α :=
    Fintype.toCompleteAtomicBooleanAlgebra α
  exact CompleteAtomicBooleanAlgebra.toSetOfIsAtom

/-- The representation of an element is precisely its set of
atoms lying beneath it. -/
theorem prebananaFiniteBooleanAtomSet_mem_iff
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (x : α) (a : PrebananaAbstractAtoms α) :
    a ∈ prebananaFiniteBooleanAtomSetOrderIso α x ↔
      (a : α) ≤ x := by
  rfl

/-- The finite powerset representation, with finite subsets
rather than arbitrary sets. -/
noncomputable def prebananaFiniteBooleanAtomFinsetEquiv
    (α : Type*) [BooleanAlgebra α] [Fintype α] :
    α ≃ Finset (PrebananaAbstractAtoms α) := by
  classical
  let e := prebananaFiniteBooleanAtomSetOrderIso α
  refine {
    toFun := fun x => (e x).toFinset
    invFun := fun s => e.symm (s : Set (PrebananaAbstractAtoms α))
    left_inv := ?_
    right_inv := ?_
  }
  · intro x
    change e.symm ((e x).toFinset : Set (PrebananaAbstractAtoms α)) = x
    simp
  · intro s
    change (e (e.symm (s : Set (PrebananaAbstractAtoms α)))).toFinset = s
    simp

/-- The stronger order isomorphism to finite atom subsets.
All Boolean operations may be transported through this order isomorphism. -/
noncomputable def prebananaFiniteBooleanAtomFinsetOrderIso
    (α : Type*) [BooleanAlgebra α] [Fintype α] :
    α ≃o Finset (PrebananaAbstractAtoms α) :=
  (prebananaFiniteBooleanAtomSetOrderIso α).trans
    ((Fintype.finsetOrderIsoSet :
      Finset (PrebananaAbstractAtoms α) ≃o
        Set (PrebananaAbstractAtoms α)).symm)

/-- The finite-atom order isomorphism preserves joins (unions). -/
theorem prebananaFiniteBooleanAtomFinsetOrderIso_sup
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (x y : α) :
    prebananaFiniteBooleanAtomFinsetOrderIso α (x ⊔ y) =
      prebananaFiniteBooleanAtomFinsetOrderIso α x ∪
      prebananaFiniteBooleanAtomFinsetOrderIso α y := by
  change prebananaFiniteBooleanAtomFinsetOrderIso α (x ⊔ y) =
    prebananaFiniteBooleanAtomFinsetOrderIso α x ⊔
    prebananaFiniteBooleanAtomFinsetOrderIso α y
  exact (prebananaFiniteBooleanAtomFinsetOrderIso α).map_sup x y

/-- The finite-atom order isomorphism preserves meets (intersections). -/
theorem prebananaFiniteBooleanAtomFinsetOrderIso_inf
    (α : Type*) [BooleanAlgebra α] [Fintype α]
    (x y : α) :
    prebananaFiniteBooleanAtomFinsetOrderIso α (x ⊓ y) =
      prebananaFiniteBooleanAtomFinsetOrderIso α x ∩
      prebananaFiniteBooleanAtomFinsetOrderIso α y := by
  change prebananaFiniteBooleanAtomFinsetOrderIso α (x ⊓ y) =
    prebananaFiniteBooleanAtomFinsetOrderIso α x ⊓
    prebananaFiniteBooleanAtomFinsetOrderIso α y
  exact (prebananaFiniteBooleanAtomFinsetOrderIso α).map_inf x y

/-- The abstract element corresponding to a finite collection
of atoms is uniquely recovered from that collection. -/
theorem prebananaFiniteBooleanAtomFinsetEquiv_injective
    (α : Type*) [BooleanAlgebra α] [Fintype α] :
    Function.Injective
      (prebananaFiniteBooleanAtomFinsetEquiv α) :=
  (prebananaFiniteBooleanAtomFinsetEquiv α).injective

end SuccessorTree.NonPrecompact

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

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Conjugate a map of finite Boolean algebras by their canonical
order isomorphisms to finite powersets of atoms. -/
noncomputable def prebananaAbstractPowersetMap
    {α β : Type*}
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (φ : α → β) :
    Finset (PrebananaAbstractAtoms α) →
      Finset (PrebananaAbstractAtoms β) :=
  fun s =>
    (prebananaFiniteBooleanAtomFinsetOrderIso β)
      (φ ((prebananaFiniteBooleanAtomFinsetOrderIso α).symm s))

theorem prebananaAbstractPowersetMap_empty
    {α β : Type*}
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (φ : α → β) (hbot : φ ⊥ = ⊥) :
    prebananaAbstractPowersetMap φ ∅ = ∅ := by
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso α
  let eB := prebananaFiniteBooleanAtomFinsetOrderIso β
  change eB (φ (eA.symm (∅ : Finset (PrebananaAbstractAtoms α)))) = ∅
  rw [show eA.symm (∅ : Finset (PrebananaAbstractAtoms α)) = (⊥ : α)
    from eA.symm.map_bot, hbot]
  exact eB.map_bot

theorem prebananaAbstractPowersetMap_univ
    {α β : Type*}
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (φ : α → β) (htop : φ ⊤ = ⊤) :
    prebananaAbstractPowersetMap φ Finset.univ = Finset.univ := by
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso α
  let eB := prebananaFiniteBooleanAtomFinsetOrderIso β
  change eB (φ (eA.symm (Finset.univ :
    Finset (PrebananaAbstractAtoms α)))) = Finset.univ
  rw [show eA.symm (Finset.univ : Finset (PrebananaAbstractAtoms α)) =
      (⊤ : α) from eA.symm.map_top, htop]
  exact eB.map_top

theorem prebananaAbstractPowersetMap_union
    {α β : Type*}
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (φ : α → β)
    (hsup : ∀ x y : α, φ (x ⊔ y) = φ x ⊔ φ y)
    (s t : Finset (PrebananaAbstractAtoms α)) :
    prebananaAbstractPowersetMap φ (s ∪ t) =
      prebananaAbstractPowersetMap φ s ∪
      prebananaAbstractPowersetMap φ t := by
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso α
  let eB := prebananaFiniteBooleanAtomFinsetOrderIso β
  change eB (φ (eA.symm (s ⊔ t))) =
    eB (φ (eA.symm s)) ⊔ eB (φ (eA.symm t))
  rw [eA.symm.map_sup, hsup, eB.map_sup]

theorem prebananaAbstractPowersetMap_inter
    {α β : Type*}
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (φ : α → β)
    (hinf : ∀ x y : α, φ (x ⊓ y) = φ x ⊓ φ y)
    (s t : Finset (PrebananaAbstractAtoms α)) :
    prebananaAbstractPowersetMap φ (s ∩ t) =
      prebananaAbstractPowersetMap φ s ∩
      prebananaAbstractPowersetMap φ t := by
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso α
  let eB := prebananaFiniteBooleanAtomFinsetOrderIso β
  change eB (φ (eA.symm (s ⊓ t))) =
    eB (φ (eA.symm s)) ⊓ eB (φ (eA.symm t))
  rw [eA.symm.map_inf, hinf, eB.map_inf]

theorem prebananaAbstractPowersetMap_injective
    {α β : Type*}
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (φ : α → β) (hinj : Function.Injective φ) :
    Function.Injective (prebananaAbstractPowersetMap φ) := by
  intro s t h
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso α
  let eB := prebananaFiniteBooleanAtomFinsetOrderIso β
  change eB (φ (eA.symm s)) = eB (φ (eA.symm t)) at h
  exact eA.symm.injective (hinj (eB.injective h))

end SuccessorTree.NonPrecompact

namespace SuccessorTree.NonPrecompact.BooleanBanana

/-- A disjoint-additive function on a finite Boolean algebra is the sum of its atom values. -/
theorem finiteAtomSum {S I V : Type*}
    [BooleanAlgebra S] [Fintype I] [DecidableEq I] [AddCommMonoid V]
    (e : S ≃o Finset I) (f : S → V)
    (hbot : f ⊥ = 0) (hadd : ∀ a b, Disjoint a b → f (a ⊔ b) = f a + f b)
    (s : Finset I) :
    ∑ i ∈ s, f (e.symm {i}) = f (e.symm s) := by
  induction s using Finset.induction_on with
  | empty =>
    change (∑ i ∈ (⊥ : Finset I), f (e.symm {i})) = f (e.symm ⊥)
    rw [e.symm.map_bot, hbot]
    exact Finset.sum_empty
  | @insert i s hi ih =>
    have hd : Disjoint ({i} : Finset I) s :=
      Finset.disjoint_singleton_left.mpr hi
    have hd' : Disjoint (e.symm {i}) (e.symm s) := by
      rw [disjoint_iff, ← e.symm.map_inf, hd.eq_bot, e.symm.map_bot]
    rw [Finset.sum_insert hi, ih, ← Finset.singleton_union, ← Finset.sup_eq_union,
      e.symm.map_sup, hadd _ _ hd']

end SuccessorTree.NonPrecompact.BooleanBanana
