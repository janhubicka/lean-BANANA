import BANANA.NonPrecompact.BinarySubspaceRamseyInterface
import SuccessorTree.ShapeFiniteCorollaries
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.List.Infix

/-!
# The binary word successor tree

This is the concrete successor tree underlying the reduction of the binary
Graham--Leeb--Rothschild theorem to the finite shape-preserving Ramsey
theorem. Nodes are finite binary words ordered by prefix; the successor
operation appends one bit and has no parameters.

The linear subspace monoid is added in the next module. Keeping the tree
interface separate makes the representation boundary easy to audit.
-/

namespace SuccessorTree.NonPrecompact

structure BinaryWord where
  bits : List F2
deriving DecidableEq

namespace BinaryWord

@[ext]
theorem ext {x y : BinaryWord} (h : x.bits = y.bits) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance : PartialOrder BinaryWord where
  le x y := x.bits <+: y.bits
  le_refl := by
    intro x
    exact List.prefix_rfl
  le_trans := by
    intro a b c hab hbc
    exact List.IsPrefix.trans hab hbc
  le_antisymm := by
    intro a b hab hba
    apply ext
    exact hab.eq_of_length
      (Nat.le_antisymm hab.length_le hba.length_le)

@[simp] theorem le_iff_prefix (x y : BinaryWord) :
    x ≤ y ↔ x.bits <+: y.bits := Iff.rfl

/-- Longest common prefix of two binary words. -/
def commonPrefix : List F2 → List F2 → List F2
  | a :: as, b :: bs =>
      if a = b then a :: commonPrefix as bs else []
  | _, _ => []

theorem commonPrefix_prefix_left :
    ∀ x y : List F2, commonPrefix x y <+: x := by
  intro x y
  induction x generalizing y with
  | nil =>
      simp [commonPrefix]
  | cons a as ih =>
      cases y with
      | nil =>
          simp [commonPrefix]
      | cons b bs =>
          by_cases h : a = b
          · subst b
            rw [commonPrefix]
            simp only [ite_true]
            exact List.cons_prefix_cons.mpr ⟨rfl, ih bs⟩
          · simp [commonPrefix, h]

theorem commonPrefix_prefix_right :
    ∀ x y : List F2, commonPrefix x y <+: y := by
  intro x y
  induction x generalizing y with
  | nil =>
      simp [commonPrefix]
  | cons a as ih =>
      cases y with
      | nil =>
          simp [commonPrefix]
      | cons b bs =>
          by_cases h : a = b
          · subst b
            rw [commonPrefix]
            simp only [ite_true]
            exact List.cons_prefix_cons.mpr ⟨rfl, ih bs⟩
          · simp [commonPrefix, h]

theorem prefix_commonPrefix :
    ∀ {z x y : List F2}, z <+: x → z <+: y →
      z <+: commonPrefix x y := by
  intro z
  induction z with
  | nil =>
      intro x y hx hy
      exact List.nil_prefix
  | cons c cs ih =>
      intro x y hx hy
      cases x with
      | nil =>
          simp at hx
      | cons a as =>
          cases y with
          | nil =>
              simp at hy
          | cons b bs =>
              obtain ⟨hca, hxt⟩ := List.cons_prefix_cons.mp hx
              obtain ⟨hcb, hyt⟩ := List.cons_prefix_cons.mp hy
              subst a
              subst b
              rw [commonPrefix]
              simp only [ite_true]
              exact List.cons_prefix_cons.mpr ⟨rfl, ih hxt hyt⟩

/-- Delete the suffix after position n. -/
def truncate (x : BinaryWord) (n : Nat) : BinaryWord :=
  ⟨x.bits.take n⟩

theorem truncate_le (x : BinaryWord) (n : Nat) :
    truncate x n ≤ x := by
  exact List.take_prefix _ _

@[simp] theorem truncate_level
    (x : BinaryWord) (n : Nat) (h : n ≤ x.bits.length) :
    (truncate x n).bits.length = n := by
  simp [truncate, List.length_take, Nat.min_eq_left h]

private theorem covBy_length_succ {a b : BinaryWord} (h : a ⋖ b) :
    b.bits.length = a.bits.length + 1 := by
  have hab : a ≤ b := h.le
  have hlt : a < b := h.lt
  have hle := hab.length_le
  have hne : a.bits.length ≠ b.bits.length := by
    intro heq
    have habEq : a.bits = b.bits := hab.eq_of_length heq
    apply hlt.ne
    exact ext habEq
  have hstrict : a.bits.length < b.bits.length := by omega
  by_contra hnot
  have hgap : a.bits.length + 1 < b.bits.length := by omega
  let c : BinaryWord := ⟨b.bits.take (a.bits.length + 1)⟩
  have hac : a < c := by
    constructor
    · change a.bits <+: b.bits.take (a.bits.length + 1)
      have htake :
          b.bits.take a.bits.length = a.bits :=
        (List.prefix_iff_eq_take.mp hab).symm
      have hpre :
          b.bits.take a.bits.length <+:
            b.bits.take (a.bits.length + 1) :=
        List.take_prefix_take_left (by omega)
      simpa [htake] using hpre
    · intro hca
      have hlen := hca.length_le
      dsimp [c] at hlen
      rw [List.length_take, Nat.min_eq_left (by omega)] at hlen
      omega
  have hcb : c < b := by
    constructor
    · change b.bits.take (a.bits.length + 1) <+: b.bits
      exact List.take_prefix _ _
    · intro hbc
      have hlen := hbc.length_le
      dsimp [c] at hlen
      rw [List.length_take, Nat.min_eq_left (by omega)] at hlen
      omega
  exact h.2 hac hcb

instance : LevelTree BinaryWord where
  level := fun x => x.bits.length
  level_lt := by
    intro a b hab
    have hle := hab.1.length_le
    have hne : a.bits.length ≠ b.bits.length := by
      intro heq
      have heqBits := hab.1.eq_of_length heq
      exact hab.2 (by
        change b.bits <+: a.bits
        rw [heqBits]
        exact List.prefix_rfl)
    omega
  covBy_level := by
    intro a b hab
    exact covBy_length_succ hab
  lower_linear := by
    intro a b c hac hbc
    by_cases hlen : a.bits.length ≤ b.bits.length
    · left
      have htakeA : c.bits.take a.bits.length = a.bits :=
        (List.prefix_iff_eq_take.mp hac).symm
      have htakeB : c.bits.take b.bits.length = b.bits :=
        (List.prefix_iff_eq_take.mp hbc).symm
      have hp :
          c.bits.take a.bits.length <+:
            c.bits.take b.bits.length :=
        List.take_prefix_take_left hlen
      change a.bits <+: b.bits
      simpa [htakeA, htakeB] using hp
    · right
      have hlen' : b.bits.length ≤ a.bits.length := by omega
      have htakeA : c.bits.take a.bits.length = a.bits :=
        (List.prefix_iff_eq_take.mp hac).symm
      have htakeB : c.bits.take b.bits.length = b.bits :=
        (List.prefix_iff_eq_take.mp hbc).symm
      have hp :
          c.bits.take b.bits.length <+:
            c.bits.take a.bits.length :=
        List.take_prefix_take_left hlen'
      change b.bits <+: a.bits
      simpa [htakeA, htakeB] using hp
  ancestor_exists := by
    intro a n hn
    refine ⟨truncate a n, truncate_le a n, ?_⟩
    exact truncate_level a n hn
  level_finite := by
    intro n
    change Set.Finite {x : BinaryWord | x.bits.length = n}
    have hfin : Set.Finite {l : List F2 | l.length = n} :=
      List.finite_length_eq F2 n
    exact Set.Finite.preimage
      (f := fun x : BinaryWord => x.bits)
      (s := {l : List F2 | l.length = n})
      (by
        intro x hx y hy hxy
        exact ext hxy)
      hfin
  meet := fun a b => ⟨commonPrefix a.bits b.bits⟩
  meet_le_left := by
    intro a b hcommon
    exact commonPrefix_prefix_left a.bits b.bits
  meet_le_right := by
    intro a b hcommon
    exact commonPrefix_prefix_right a.bits b.bits
  le_meet := by
    intro a b c hca hcb
    exact prefix_commonPrefix hca hcb

/-- Append one bit. -/
def appendBit (x : BinaryWord) (b : F2) : BinaryWord :=
  ⟨x.bits ++ [b]⟩

theorem covBy_appendBit (x : BinaryWord) (b : F2) :
    x ⋖ appendBit x b := by
  refine ⟨?_, ?_⟩
  · constructor
    · exact List.prefix_append _ _
    · intro h
      have hlen := h.length_le
      simp [appendBit] at hlen
  · intro z hxz hzb
    have hzx := LevelTree.lt_level_lt hxz
    have hzbLen := LevelTree.lt_level_lt hzb
    change x.bits.length < z.bits.length at hzx
    change z.bits.length < (x.bits ++ [b]).length at hzbLen
    simp only [List.length_append, List.length_singleton,
      Nat.add_one] at hzbLen
    omega

/-- The parameter-free binary successor operation. -/
def binaryWordSTree : STree BinaryWord F2 where
  succ := fun a p c =>
    if p = [] then some (appendBit a c) else none
  s1 := by
    intro a p c b h
    split at h
    next hp =>
      subst p
      simp only [Option.some.injEq] at h
      subst b
      refine ⟨covBy_appendBit a c, ?_⟩
      simp
    next hp =>
      simp at h
  s2 := by
    intro a b x p q c d ha hb
    split at ha
    next hp =>
      subst p
      simp only [Option.some.injEq] at ha
      subst x
      split at hb
      next hq =>
        subst q
        simp only [Option.some.injEq] at hb
        have hbits := congrArg BinaryWord.bits hb
        simp [appendBit] at hbits
        exact ⟨ext hbits.1.symm, rfl, hbits.2.symm⟩
      next hq =>
        simp at hb
    next hp =>
      simp at ha
  s3 := by
    intro a b hab
    have hlen : b.bits.length = a.bits.length + 1 :=
      covBy_length_succ hab
    have hpre : a.bits <+: b.bits := hab.le
    obtain ⟨tail, htail⟩ := hpre
    have hlen' := congrArg List.length htail
    simp only [List.length_append] at hlen'
    have htail_len : tail.length = 1 := by
      omega
    obtain ⟨c, rfl⟩ := List.length_eq_one.mp htail_len
    refine ⟨[], c, ?_⟩
    change
      (if ([] : List BinaryWord) = [] then
          some (appendBit a c) else none) = some b
    simp only [ite_true, Option.some.injEq]
    apply ext
    exact htail

end BinaryWord

end SuccessorTree.NonPrecompact
