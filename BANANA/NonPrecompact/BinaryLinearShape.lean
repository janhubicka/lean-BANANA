import BANANA.NonPrecompact.BinaryWordTree

/-!
# Levelwise-linear shape maps on the binary word tree

A shape map of the binary word tree is called linear when, on every source
level, it preserves zero and binary addition.  The label-preserving shape-map
axioms then put these linear maps automatically in row-echelon form.

This characterisation is convenient for the GLR reduction: identity,
composition and fusion are immediate at the level of the linear laws, while
the one-level factorisation is handled separately by finite-dimensional
linear algebra.
-/

namespace SuccessorTree.NonPrecompact

open SuccessorTree
open BinaryWord

namespace BinaryWord

/-- The zero word of a prescribed length. -/
def zero (n : Nat) : BinaryWord :=
  ⟨List.replicate n 0⟩

@[simp] theorem zero_length (n : Nat) :
    (zero n).bits.length = n := by
  simp [zero]

/-- Coordinatewise binary addition. -/
def add (x y : BinaryWord) : BinaryWord :=
  ⟨List.zipWith (· + ·) x.bits y.bits⟩

@[simp] theorem add_length (x y : BinaryWord) :
    (add x y).bits.length = min x.bits.length y.bits.length := by
  simp [add, List.length_zipWith]

@[simp] theorem add_length_of_eq
    {x y : BinaryWord} (h : x.bits.length = y.bits.length) :
    (add x y).bits.length = x.bits.length := by
  simp [add_length, h]

end BinaryWord

/-- A binary-tree shape map is linear on every level. -/
def BinaryLevelLinear
    (F : ShapeMap BinaryWord.binaryWordSTree) : Prop :=
  (∀ n : Nat,
      F (BinaryWord.zero n) =
        BinaryWord.zero ((F (BinaryWord.zero n)).bits.length)) ∧
  (∀ x y : BinaryWord,
      x.bits.length = y.bits.length →
      F (BinaryWord.add x y) =
        BinaryWord.add (F x) (F y))

namespace BinaryLevelLinear

theorem id :
    BinaryLevelLinear
      (ShapeMap.id BinaryWord.binaryWordSTree) := by
  constructor
  · intro n
    rfl
  · intro x y h
    rfl

theorem comp
    {F G : ShapeMap BinaryWord.binaryWordSTree}
    (hF : BinaryLevelLinear F)
    (hG : BinaryLevelLinear G) :
    BinaryLevelLinear (F.comp G) := by
  rcases hF with ⟨hF0, hFadd⟩
  rcases hG with ⟨hG0, hGadd⟩
  constructor
  · intro n
    rw [ShapeMap.comp_apply, hG0 n]
    exact hF0 ((G (BinaryWord.zero n)).bits.length)
  · intro x y hxy
    rw [ShapeMap.comp_apply, hGadd x y hxy]
    have hlevels :
        (G x).bits.length = (G y).bits.length := by
      exact G.level_eq_of_level_eq hxy
    rw [hFadd (G x) (G y) hlevels]
    rfl

theorem fusion
    (F : Nat → ShapeMap BinaryWord.binaryWordSTree)
    (hlin : ∀ i, BinaryLevelLinear (F i))
    (hstable : ShapeMap.FusionStable F) :
    BinaryLevelLinear (ShapeMap.fusionLimit F hstable) := by
  constructor
  · intro n
    have hstage := (hlin n).1 n
    change
      (ShapeMap.fusionLimit F hstable (BinaryWord.zero n)) =
        BinaryWord.zero
          ((ShapeMap.fusionLimit F hstable (BinaryWord.zero n)).bits.length)
    rw [ShapeMap.fusionLimit_apply]
    simpa using hstage
  · intro x y hxy
    let n := x.bits.length
    have hy : y.bits.length = n := by
      simpa [n] using hxy.symm
    have hadd : (BinaryWord.add x y).bits.length = n := by
      simpa [n, hxy] using BinaryWord.add_length_of_eq hxy
    have hstage := (hlin n).2 x y hxy
    change
      ShapeMap.fusionLimit F hstable (BinaryWord.add x y) =
        BinaryWord.add
          (ShapeMap.fusionLimit F hstable x)
          (ShapeMap.fusionLimit F hstable y)
    rw [ShapeMap.fusionLimit_apply,
      show LevelTree.lev x = n by rfl,
      ShapeMap.fusionLimit_apply,
      show LevelTree.lev y = n by simpa [hy],
      ShapeMap.fusionLimit_apply,
      show LevelTree.lev (BinaryWord.add x y) = n by simpa using hadd]
    exact hstage

end BinaryLevelLinear

end SuccessorTree.NonPrecompact
