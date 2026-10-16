import BANANA.NonPrecompact.PrebananaFiveAryBooleanStage
import Mathlib.Data.Set.Countable

/-!
# A countable concrete carrier for the five-ary pre-BANANA limit

A Boolean element at level n is a finite set of n-letter words.
Represent it as the cylinder of infinite five-ary sequences whose
n-letter prefix belongs to that set. This avoids an arbitrary-choice
representative in a direct-limit quotient and retains the actual
finite-stage embeddings.

This module proves only the countable carrier, injective stage maps
and basic cylinder set operations. The Boolean-algebra structure,
well-defined marking, finite age, extension property and
ultrahomogeneity are separate forthcoming steps.
-/

namespace SuccessorTree.NonPrecompact

/-- Infinite five-ary branches. -/
abbrev PrebananaFiveAryInfiniteWord := ℕ → Fin 5

/-- The prefix of length n of an infinite branch. -/
def prebananaFiveAryInfinitePrefix (n : ℕ)
    (w : PrebananaFiveAryInfiniteWord) : PrebananaFiveAryWord n :=
  fun i => w i

/-- Extend a finite word to an infinite branch, with zeroes afterwards. -/
def prebananaFiveAryExtendWord (n : ℕ)
    (v : PrebananaFiveAryWord n) : PrebananaFiveAryInfiniteWord :=
  fun i => if h : i < n then v ⟨i, h⟩ else 0

@[simp]
theorem prebananaFiveAryInfinitePrefix_extend (n : ℕ)
    (v : PrebananaFiveAryWord n) :
    prebananaFiveAryInfinitePrefix n (prebananaFiveAryExtendWord n v) = v := by
  funext i
  simp [prebananaFiveAryInfinitePrefix, prebananaFiveAryExtendWord, i.isLt]

/-- The cylinder determined by a finite set of length-n words. -/
def prebananaFiveAryCylinder (n : ℕ)
    (s : Finset (PrebananaFiveAryWord n)) :
    Set PrebananaFiveAryInfiniteWord :=
  {w | prebananaFiveAryInfinitePrefix n w ∈ s}

/-- Cylinder representation at each fixed level is injective. -/
theorem prebananaFiveAryCylinder_injective (n : ℕ) :
    Function.Injective (prebananaFiveAryCylinder n) := by
  intro s t h
  ext v
  have hh := congrArg
    (fun X : Set PrebananaFiveAryInfiniteWord =>
      prebananaFiveAryExtendWord n v ∈ X) h
  simpa [prebananaFiveAryCylinder,
    prebananaFiveAryInfinitePrefix_extend] using hh

@[simp] theorem prebananaFiveAryCylinder_empty (n : ℕ) :
    prebananaFiveAryCylinder n ∅ = ∅ := by
  ext w
  simp [prebananaFiveAryCylinder]

@[simp] theorem prebananaFiveAryCylinder_univ (n : ℕ) :
    prebananaFiveAryCylinder n Finset.univ = Set.univ := by
  ext w
  simp [prebananaFiveAryCylinder]

theorem prebananaFiveAryCylinder_union (n : ℕ)
    (s t : Finset (PrebananaFiveAryWord n)) :
    prebananaFiveAryCylinder n (s ∪ t) =
      prebananaFiveAryCylinder n s ∪ prebananaFiveAryCylinder n t := by
  ext w
  simp [prebananaFiveAryCylinder]

theorem prebananaFiveAryCylinder_inter (n : ℕ)
    (s t : Finset (PrebananaFiveAryWord n)) :
    prebananaFiveAryCylinder n (s ∩ t) =
      prebananaFiveAryCylinder n s ∩ prebananaFiveAryCylinder n t := by
  ext w
  simp [prebananaFiveAryCylinder]

theorem prebananaFiveAryCylinder_compl (n : ℕ)
    (s : Finset (PrebananaFiveAryWord n)) :
    prebananaFiveAryCylinder n (Finset.univ \ s) =
      (prebananaFiveAryCylinder n s)ᶜ := by
  ext w
  simp [prebananaFiveAryCylinder]

/-- The candidate direct-limit carrier: cylinder subsets of infinite
branches, with a finite-stage presentation. -/
def PrebananaFiveAryCylinderLimitCarrier : Type :=
  {X : Set PrebananaFiveAryInfiniteWord //
    ∃ n : ℕ, ∃ s : Finset (PrebananaFiveAryWord n),
      X = prebananaFiveAryCylinder n s}

/-- The actual finite stage embeds faithfully into the cylinder carrier. -/
noncomputable def prebananaFiveAryCylinderStageEmbedding (n : ℕ) :
    (prebananaFiveAryBooleanStage n).carrier ↪
      PrebananaFiveAryCylinderLimitCarrier where
  toFun := fun s => ⟨prebananaFiveAryCylinder n s, ⟨n, s, rfl⟩⟩
  inj' := by
    intro s t h
    apply prebananaFiveAryCylinder_injective n
    exact congrArg Subtype.val h

/-- The cylinder carrier is countable, because every element comes
from a finite word level and there are countably many finite levels. -/
noncomputable instance : Countable PrebananaFiveAryCylinderLimitCarrier := by
  classical
  let present :
      (Σ n : ℕ, Finset (PrebananaFiveAryWord n)) →
      PrebananaFiveAryCylinderLimitCarrier :=
    fun ⟨n, s⟩ =>
      ⟨prebananaFiveAryCylinder n s, ⟨n, s, rfl⟩⟩
  have hsurj : Function.Surjective present := by
    rintro ⟨X, ⟨n, s, hX⟩⟩
    refine ⟨⟨n, s⟩, ?_⟩
    apply Subtype.ext
    change prebananaFiveAryCylinder n s = X
    exact hX.symm
  have hcount : (Set.range present).Countable :=
    Set.countable_range present
  have hrange :
      Set.range present =
        (Set.univ : Set PrebananaFiveAryCylinderLimitCarrier) :=
    Set.range_eq_univ.mpr hsurj
  rw [hrange] at hcount
  exact (Set.countable_univ_iff).mp hcount

end SuccessorTree.NonPrecompact
