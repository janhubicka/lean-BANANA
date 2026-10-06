import BANANA.NonPrecompact.BinarySubspaceRamseyInterface
import SuccessorTree.ShapeFiniteCorollaries
import Mathlib.Data.Set.Finite.List

/-!
# The binary word successor tree

This is the concrete successor tree underlying the reduction of the binary
Graham--Leeb--Rothschild theorem to the finite shape-preserving Ramsey
theorem.  Nodes are finite binary words ordered by prefix; the successor
operation appends one bit and has no parameters.

The linear subspace monoid is added in the next module.  Keeping the tree
interface separate makes the representation boundary easy to audit.
-/

namespace SuccessorTree.NonPrecompact

open SuccessorTree

structure BinaryWord where
  bits : List F2
deriving DecidableEq

namespace BinaryWord

instance : LE BinaryWord :=
  ⟨fun x y => x.bits <+: y.bits⟩

instance : LT BinaryWord :=
  ⟨fun x y => x ≤ y ∧ x ≠ y⟩

instance : PartialOrder BinaryWord where
  le_refl x := List.prefix_rfl
  le_trans _ _ _ hxy hyz := hxy.trans hyz
  le_antisymm x y hxy hyx := by
    apply BinaryWord.ext
    exact hxy.eq_of_length (hxy.length_le.antisymm hyx.length_le)
  lt_iff_le_not_le := by
    intro x y
    constructor
    · rintro ⟨hxy, hne⟩
      refine ⟨hxy, ?_⟩
      intro hyx
      exact hne (le_antisymm hxy hyx)
    · rintro ⟨hxy, hnyx⟩
      exact ⟨hxy, fun h => hnyx (by simpa [h])⟩

@[simp] theorem le_iff_prefix (x y : BinaryWord) :
    x ≤ y ↔ x.bits <+: y.bits := Iff.rfl

@[simp] theorem level_def (x : BinaryWord) :
    x.bits.length = x.bits.length := rfl

/-- Longest common prefix of two binary words. -/
def commonPrefix : List F2 → List F2 → List F2
  | a :: as, b :: bs =>
      if h : a = b then a :: commonPrefix as bs else []
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

instance : LevelTree BinaryWord where
  level := fun x => x.bits.length
  level_lt := by
    intro a b hab
    have hle : a.bits.length ≤ b.bits.length := hab.1.length_le
    have hne : a.bits.length ≠ b.bits.length := by
      intro h
      apply hab.2
      apply BinaryWord.ext
      exact hab.1.eq_of_length h
    omega
  covBy_level := by
    intro a b hab
    have hp : a.bits <+: b.bits := hab.1.1
    obtain ⟨tail, htail⟩ := hp
    have htail_ne : tail ≠ [] := by
      intro h
      apply hab.1.2
      apply BinaryWord.ext
      simpa [h, htail]
    cases tail with
    | nil =>
        exact False.elim (htail_ne rfl)
    | cons c tail =>
        cases tail with
        | nil =>
            simp [htail]
        | cons d tail =>
            let mid : BinaryWord := ⟨a.bits ++ [c]⟩
            have hamid : a < mid := by
              constructor
              · exact ⟨[c], rfl⟩
              · intro h
                have hl := congrArg (fun z : BinaryWord => z.bits.length) h
                simp [mid] at hl
            have hmidb : mid < b := by
              constructor
              · refine ⟨d :: tail, ?_⟩
                simp [mid, htail, List.append_assoc]
              · intro h
                have hl := congrArg (fun z : BinaryWord => z.bits.length) h
                simp [mid, htail] at hl
            exact False.elim ((hab.2 mid hamid hmidb))
  lower_linear := by
    intro a b c hac hbc
    by_cases hlen : a.bits.length ≤ b.bits.length
    · left
      rw [List.prefix_iff_eq_take] at hac ⊢
      rw [hac]
      simpa [List.take_take, Nat.min_eq_left hlen]
    · right
      have hlen' : b.bits.length ≤ a.bits.length := by omega
      rw [List.prefix_iff_eq_take] at hbc ⊢
      rw [hbc]
      simpa [List.take_take, Nat.min_eq_left hlen']
  ancestor_exists := by
    intro a n hn
    refine ⟨truncate a n, truncate_le a n, ?_⟩
    exact truncate_level a n hn
  level_finite := by
    intro n
    let f : BinaryWord → List F2 := BinaryWord.bits
    have hinj : Function.Injective f := by
      intro x y h
      exact BinaryWord.ext h
    have hfin : Set.Finite {l : List F2 | l.length = n} :=
      List.finite_length_eq F2 n
    exact hfin.preimage f hinj
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

/-- The parameter-free binary successor operation. -/
def binaryWordSTree : STree BinaryWord F2 where
  succ a p c :=
    if p = [] then some ⟨a.bits ++ [c]⟩ else none
  s1 := by
    intro a p c b h
    split at h
    next hp =>
      subst p
      simp only [Option.some.injEq] at h
      subst b
      constructor
      · apply LevelTree.covBy_of_le_level_succ
        · exact ⟨[c], rfl⟩
        · simp
      · simp
    next hp =>
      simp at h
  s2 := by
    intro a b x p q c d ha hb
    split at ha
    next hp =>
      subst p
      split at hb
      next hq =>
        subst q
        simp only [Option.some.injEq] at ha hb
        have heq : a.bits ++ [c] = b.bits ++ [d] := by
          simpa [ha, hb]
        have hlen : a.bits.length = b.bits.length := by
          have := congrArg List.length heq
          simpa using this
        have hab : a.bits = b.bits := by
          have ht := congrArg (List.take a.bits.length) heq
          simpa [hlen] using ht
        have hcd : c = d := by
          have ht := congrArg List.getLast? heq
          simpa using ht
        exact ⟨BinaryWord.ext hab, rfl, hcd⟩
      next hq =>
        simp at hb
    next hp =>
      simp at ha
  s3 := by
    intro a b hab
    have hpre : a.bits <+: b.bits := hab.1.le
    obtain ⟨tail, htail⟩ := hpre
    have hlen := LevelTree.covBy_level_eq hab
    change b.bits.length = a.bits.length + 1 at hlen
    have htail_len : tail.length = 1 := by
      simpa [htail] using hlen
    obtain ⟨c, rfl⟩ := List.length_eq_one.mp htail_len
    refine ⟨[], c, ?_⟩
    simp [binaryWordSTree, htail]

end BinaryWord

end SuccessorTree.NonPrecompact
