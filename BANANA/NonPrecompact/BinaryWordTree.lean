import BANANA.NonPrecompact.BinarySubspaceRamseyFromSuccessor
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.List.Infix

/-!
# The binary prefix successor tree

This is the concrete levelled tree underlying the successor-tree proof of the
binary finite-vector-space Ramsey theorem.  A node is a finite binary word,
ordered by prefix.  Level is word length and the successor operation appends
one bit.

The distinguished monoid used for vector spaces is added separately: its
members are the prefix-tree shape maps whose action on every level is linear.
Keeping the bare tree in a separate file makes the representation boundary
easy to audit.
-/

namespace SuccessorTree.NonPrecompact

/-- A wrapper around finite F₂-words, used so that the prefix order can be the
ambient partial order without interfering with other list orders. -/
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

instance : LE BinaryWord :=
  ⟨fun x y => x.bits <+: y.bits⟩

instance : LT BinaryWord :=
  ⟨fun x y => x ≤ y ∧ ¬ y ≤ x⟩

instance : PartialOrder BinaryWord where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := by
    intro x
    exact List.prefix_rfl
  le_trans := by
    intro a b c hab hbc
    exact hab.trans hbc
  le_antisymm := by
    intro a b hab hba
    apply ext
    exact hab.eq_of_length
      (Nat.le_antisymm hab.length_le hba.length_le)
  lt_iff_le_not_le := Iff.rfl

@[simp] theorem le_iff {x y : BinaryWord} :
    x ≤ y ↔ x.bits <+: y.bits := Iff.rfl

@[simp] theorem level_bits (x : BinaryWord) :
    x.bits.length = x.bits.length := rfl

/-- Longest common prefix, defined recursively so that no choice is hidden in
the tree meet. -/
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
            simp only [commonPrefix, if_pos rfl]
            exact List.IsPrefix.cons (ih bs)
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
            simp only [commonPrefix, if_pos rfl]
            exact List.IsPrefix.cons (ih bs)
          · simp [commonPrefix, h]

theorem prefix_commonPrefix :
    ∀ {z x y : List F2}, z <+: x → z <+: y →
      z <+: commonPrefix x y := by
  intro z x y hzx hzy
  induction z generalizing x y with
  | nil =>
      exact List.nil_prefix
  | cons c cs ih =>
      cases x with
      | nil =>
          simp at hzx
      | cons a as =>
          cases y with
          | nil =>
              simp at hzy
          | cons b bs =>
              have hca : c = a := by
                rcases hzx with ⟨t, ht⟩
                cases ht
                rfl
              have hcb : c = b := by
                rcases hzy with ⟨t, ht⟩
                cases ht
                rfl
              subst a
              subst b
              have hzx' : cs <+: as := by
                rcases hzx with ⟨t, ht⟩
                simpa using (List.cons.inj ht).2
              have hzy' : cs <+: bs := by
                rcases hzy with ⟨t, ht⟩
                simpa using List.cons.inj ht |>.2
              simp only [commonPrefix, if_pos rfl]
              exact List.IsPrefix.cons (ih hzx' hzy')

/-- Prefix-tree meet. -/
def meet (x y : BinaryWord) : BinaryWord :=
  ⟨commonPrefix x.bits y.bits⟩

/-- Taking a prefix at a prescribed length. -/
def ancestor (x : BinaryWord) (n : Nat) : BinaryWord :=
  ⟨x.bits.take n⟩

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
      rcases hab with ⟨t, ht⟩
      have htake :
          b.bits.take a.bits.length = a.bits := by
        subst b
        simp
      have hlen :
          a.bits.length ≤ a.bits.length + 1 := by omega
      have hpre :
          b.bits.take a.bits.length <+:
            b.bits.take (a.bits.length + 1) :=
        List.take_prefix_take_left hlen
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
  exact (h.2 hac hcb)

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
      rcases hbc with ⟨tb, hcb⟩
      rcases hac with ⟨ta, hca⟩
      have htakeA : c.bits.take a.bits.length = a.bits := by
        rw [hca]
        simp
      have htakeB : c.bits.take b.bits.length = b.bits := by
        rw [hcb]
        simp
      have hp :
          c.bits.take a.bits.length <+:
            c.bits.take b.bits.length :=
        List.take_prefix_take_left hlen
      change a.bits <+: b.bits
      simpa [htakeA, htakeB] using hp
    · right
      have hlen' : b.bits.length ≤ a.bits.length := by omega
      rcases hbc with ⟨tb, hcb⟩
      rcases hac with ⟨ta, hca⟩
      have htakeA : c.bits.take a.bits.length = a.bits := by
        rw [hca]
        simp
      have htakeB : c.bits.take b.bits.length = b.bits := by
        rw [hcb]
        simp
      have hp :
          c.bits.take b.bits.length <+:
            c.bits.take a.bits.length :=
        List.take_prefix_take_left hlen'
      change b.bits <+: a.bits
      simpa [htakeA, htakeB] using hp
  ancestor_exists := by
    intro a n hn
    refine ⟨ancestor a n, ?_, ?_⟩
    · change a.bits.take n <+: a.bits
      exact List.take_prefix _ _
    · simp [ancestor, Nat.min_eq_left hn]
  level_finite := by
    intro n
    change Set.Finite {x : BinaryWord | x.bits.length = n}
    have hfin : Set.Finite {l : List F2 | l.length = n} :=
      List.finite_length_eq F2 n
    exact hfin.preimage (fun x : BinaryWord => x.bits) (by
      intro x y h
      exact ext h)
  meet := meet
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
    have hzx := hxz.1.length_le
    have hzbLen := hzb.1.length_le
    simp [appendBit] at hzbLen
    omega

/-- Binary successor operation: parameters are empty and the character is the
new bit. -/
def binarySucc : STree BinaryWord F2 where
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
        have hlen : a.bits.length = b.bits.length := by
          have h := congrArg List.length hbits
          simp at h
          omega
        have hab : a.bits = b.bits := by
          have htake :=
            congrArg (fun l : List F2 => l.take a.bits.length) hbits
          simpa [hlen] using htake
        have hcd : c = d := by
          rw [hab] at hbits
          have hsingle : [c] = [d] :=
            List.append_left_cancel hbits
          exact List.singleton_inj.mp hsingle
        exact ⟨ext hab, rfl, hcd⟩
      next hq =>
        simp at hb
    next hp =>
      simp at ha
  s3 := by
    intro a b hab
    have hlen : b.bits.length = a.bits.length + 1 :=
      covBy_length_succ hab
    have hpref : a.bits <+: b.bits := hab.le
    rcases hpref with ⟨t, ht⟩
    have htlen : t.length = 1 := by
      subst b
      simp at hlen
      omega
    obtain ⟨c, rfl⟩ : ∃ c : F2, t = [c] := by
      cases t with
      | nil => simp at htlen
      | cons c t =>
          cases t with
          | nil => exact ⟨c, rfl⟩
          | cons d t =>
              simp at htlen
    refine ⟨[], c, ?_⟩
    simp [binarySucc, appendBit, ht]

end BinaryWord

end SuccessorTree.NonPrecompact
