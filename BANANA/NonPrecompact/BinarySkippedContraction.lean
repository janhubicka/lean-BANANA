import BANANA.NonPrecompact.LinearBinaryDuplication

/-!
# Contracting a skipped binary coordinate

This is the order-theoretic half of M2 for the linear binary successor
instance.  If a shape map omits target level `t`, erase coordinate `t`
from every value.  The result is again a shape map.

Injectivity is the only nontrivial point.  If two distinct images became
equal after deleting coordinate `t`, their longest common prefix would end
exactly at level `t`.  Shape maps preserve meets, contradicting that level
`t` is skipped.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

/-- Delete coordinate `t`; when the word is too short, this is the identity. -/
def eraseCoordinate (t : ℕ) (w : BinaryWord) : BinaryWord :=
  ⟨w.bits.eraseIdx t⟩

theorem eraseCoordinate_le_of_le
    {t : ℕ} {x y : BinaryWord} (h : x ≤ y) :
    eraseCoordinate t x ≤ eraseCoordinate t y :=
  h.eraseIdx t

theorem eraseCoordinate_length
    (t : ℕ) (w : BinaryWord) :
    (eraseCoordinate t w).bits.length =
      if t < w.bits.length then w.bits.length - 1 else w.bits.length := by
  by_cases h : t < w.bits.length
  · simp [eraseCoordinate, h, List.length_eraseIdx_of_lt]
  · have hle : w.bits.length ≤ t := Nat.le_of_not_gt h
    rw [eraseCoordinate, List.eraseIdx_of_length_le hle]
    simp [h]

/-- Deleting a coordinate other than the newly appended last coordinate
commutes with appending the last bit. -/
theorem eraseCoordinate_appendBit
    (t : ℕ) (w : BinaryWord) (c : F2)
    (hne : w.bits.length ≠ t) :
    eraseCoordinate t (appendBit w c) =
      appendBit (eraseCoordinate t w) c := by
  apply BinaryWord.ext
  change
    (w.bits ++ [c]).eraseIdx t =
      w.bits.eraseIdx t ++ [c]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : w.bits.length ≤ t := Nat.le_of_lt hlt
    rw [List.eraseIdx_append_of_length_le hle,
      List.eraseIdx_of_length_le hle]
    have hpos : 1 ≤ t - w.bits.length := by omega
    rw [List.eraseIdx_of_length_le]
    simp
    simpa using hpos
  · exact List.eraseIdx_append_of_lt_length hgt [c]

/-- If two equal-length distinct lists become equal after deleting coordinate
`t`, their longest common prefix has length exactly `t`. -/
theorem commonPrefix_length_of_eraseIdx_eq
    {x y : List F2} {t L : ℕ}
    (hx : x.length = L) (hy : y.length = L)
    (ht : t < L)
    (herase : x.eraseIdx t = y.eraseIdx t)
    (hne : x ≠ y) :
    (commonPrefix x y).length = t := by
  have htake : x.take t = y.take t := by
    calc
      x.take t = (x.eraseIdx t).take t := by
        symm
        exact List.take_eraseIdx_eq_take_of_le x t t le_rfl
      _ = (y.eraseIdx t).take t := by rw [herase]
      _ = y.take t :=
        List.take_eraseIdx_eq_take_of_le y t t le_rfl
  have hxpre : x.take t <+: x := List.take_prefix _ _
  have hypre : x.take t <+: y := by
    rw [htake]
    exact List.take_prefix _ _
  have hlowpre :
      x.take t <+: commonPrefix x y :=
    prefix_commonPrefix hxpre hypre
  have htakeLen : (x.take t).length = t := by
    simp [hx, Nat.min_eq_left (Nat.le_of_lt (hx ▸ ht))]
  have hlow : t ≤ (commonPrefix x y).length := by
    simpa [htakeLen] using hlowpre.length_le
  have hupper : (commonPrefix x y).length ≤ t := by
    by_contra hnot
    have htc : t < (commonPrefix x y).length := by omega
    have hpx := commonPrefix_prefix_left x y
    have hpy := commonPrefix_prefix_right x y
    have hcoord : x[t] = y[t] := by
      have hxv := hpx.getElem htc
      have hyv := hpy.getElem htc
      exact hxv.symm.trans hyv
    have hxrec := List.insertIdx_eraseIdx_getElem (l := x) (n := t) (hx ▸ ht)
    have hyrec := List.insertIdx_eraseIdx_getElem (l := y) (n := t) (hy ▸ ht)
    apply hne
    calc
      x = (x.eraseIdx t).insertIdx t x[t] := hxrec.symm
      _ = (y.eraseIdx t).insertIdx t y[t] := by
        rw [herase, hcoord]
      _ = y := hyrec
  exact Nat.le_antisymm hupper hlow

/-- The coordinate-deletion length transform is injective on lengths other
than the deleted level. -/
theorem eraseCoordinate_length_injective_off
    {t a b : ℕ} (ha : a ≠ t) (hb : b ≠ t)
    (h :
      (if t < a then a - 1 else a) =
        (if t < b then b - 1 else b)) :
    a = b := by
  by_cases hat : t < a
  · by_cases hbt : t < b
    · simp [hat, hbt] at h
      omega
    · have hble : b ≤ t := Nat.le_of_not_gt hbt
      have hage : t + 1 ≤ a := by omega
      simp [hat, hbt] at h
      omega
  · have hale : a ≤ t := Nat.le_of_not_gt hat
    by_cases hbt : t < b
    · have hbge : t + 1 ≤ b := by omega
      simp [hat, hbt] at h
      omega
    · simp [hat, hbt] at h
      exact h

/-- Erase a target coordinate globally from a shape map which skips that
target level. -/
def contractSkipped
    (F : ShapeMap binarySucc) (t : ℕ)
    (hskip : F.Skips t) :
    ShapeMap binarySucc where
  toFun := fun w => eraseCoordinate t (F w)
  injective' := by
    intro x y hxy
    have hlenxy :=
      congrArg (fun z : BinaryWord => z.bits.length) hxy
    rw [eraseCoordinate_length, eraseCoordinate_length] at hlenxy
    have hFxNe : (F x).bits.length ≠ t := by
      intro heq
      exact hskip ⟨x, heq⟩
    have hFyNe : (F y).bits.length ≠ t := by
      intro heq
      exact hskip ⟨y, heq⟩
    have hlenF :
        (F x).bits.length = (F y).bits.length :=
      eraseCoordinate_length_injective_off hFxNe hFyNe hlenxy
    by_cases hF : F x = F y
    · exact F.injective hF
    have htFx : t < (F x).bits.length := by
      by_contra hnot
      have hle : (F x).bits.length ≤ t := Nat.le_of_not_gt hnot
      have hlt : (F x).bits.length < t := lt_of_le_of_ne hle hFxNe
      have hltY : (F y).bits.length < t := by simpa [hlenF] using hlt
      have hxid : eraseCoordinate t (F x) = F x := by
        apply BinaryWord.ext
        simp [eraseCoordinate, List.eraseIdx_of_length_le (Nat.le_of_lt hlt)]
      have hyid : eraseCoordinate t (F y) = F y := by
        apply BinaryWord.ext
        simp [eraseCoordinate, List.eraseIdx_of_length_le (Nat.le_of_lt hltY)]
      exact hF (hxid.symm.trans (hxy.trans hyid))
    have hcp :
        (commonPrefix (F x).bits (F y).bits).length = t :=
      commonPrefix_length_of_eraseIdx_eq
        rfl hlenF.symm htFx
        (congrArg BinaryWord.bits hxy) (by
          intro h
          apply hF
          exact BinaryWord.ext h)
    let root : BinaryWord := ⟨[]⟩
    have hcommon : ∃ r : BinaryWord, r ≤ x ∧ r ≤ y :=
      ⟨root, List.nil_prefix, List.nil_prefix⟩
    have hmeet := F.map_meet hcommon
    have hlev :
        LevelTree.lev (F (LevelTree.meet x y)) = t := by
      rw [hmeet]
      exact hcp
    exact False.elim (hskip ⟨LevelTree.meet x y, hlev⟩)
  level_preserving' := by
    intro x y hxy
    have hFxy := F.level_eq_of_level_eq hxy
    change
      (eraseCoordinate t (F x)).bits.length =
        (eraseCoordinate t (F y)).bits.length
    rw [eraseCoordinate_length, eraseCoordinate_length]
    change (F x).bits.length = (F y).bits.length at hFxy
    rw [hFxy]
  weak_succ' := by
    intro a b p c hs
    obtain ⟨d, hFd, hdb⟩ := F.weak_succ' hs
    have hp : p = [] := by
      change
        (if p = [] then some (appendBit a c) else none) = some b at hs
      by_contra hp
      simp [hp] at hs
    subst p
    have hFd' : d = appendBit (F a) c := by
      change
        (if ([] : List BinaryWord) = [] then
            some (appendBit (F a) c) else none) = some d at hFd
      simpa using hFd.symm
    subst d
    have hFaNe : (F a).bits.length ≠ t := by
      intro heq
      exact hskip ⟨a, heq⟩
    refine ⟨eraseCoordinate t (appendBit (F a) c), ?_, ?_⟩
    · rw [eraseCoordinate_appendBit t (F a) c hFaNe]
      simp [binarySucc]
    · exact eraseCoordinate_le_of_le hdb
  root_le' := by
    intro a ha
    change a.bits.length = 0 at ha
    have ha0 : a.bits = [] := List.length_eq_zero_iff.mp ha
    change a.bits <+: (eraseCoordinate t (F a)).bits
    rw [ha0]
    exact List.nil_prefix

@[simp] theorem contractSkipped_apply
    (F : ShapeMap binarySucc) (t : ℕ)
    (hskip : F.Skips t) (w : BinaryWord) :
    contractSkipped F t hskip w = eraseCoordinate t (F w) := rfl

end BinaryWord
end SuccessorTree.NonPrecompact
