import BANANA.NonPrecompact.BinarySkippedContraction
import BANANA.NonPrecompact.LinearBinaryMonoidBasic

/-!
# Linearity of skipped-coordinate contraction

The skipped-coordinate contraction preserves the linear binary monoid.
Above the deleted coordinate this is just composition with the linear
coordinate-removal map Fin.removeNth; below it, contraction is the identity.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

/-- Coordinate removal as a linear map. -/
def removeNthLinearMap
    {k : ℕ} (p : Fin (k + 1)) :
    (Fin (k + 1) → F2) →ₗ[F2] (Fin k → F2) where
  toFun := fun x => p.removeNth x
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl

/-- List.eraseIdx on a word level agrees with Fin.removeNth on its
coordinate vector. -/
theorem levelEquiv_eraseCoordinate
    {k : ℕ} (p : Fin (k + 1))
    (w : AtLevel (k + 1)) :
    let hlen :
        (eraseCoordinate p.1 w.1).bits.length = k := by
      change (w.1.bits.eraseIdx p.1).length = k
      rw [List.length_eraseIdx_of_lt]
      · omega
      · simpa [w.2] using p.2
    levelEquiv k ⟨eraseCoordinate p.1 w.1, hlen⟩ =
      removeNthLinearMap p (levelEquiv (k + 1) w) := by
  intro hlen
  funext i
  change
    (w.1.bits.eraseIdx p.1).get
      ⟨i.1, by simpa [hlen] using i.2⟩ =
    w.1.bits.get
      ⟨(p.succAbove i).1,
        by simpa [w.2] using (p.succAbove i).2⟩
  rw [List.getElem_eraseIdx]
  by_cases hi : i.1 < p.1
  · rw [dif_pos hi]
    have hs : p.succAbove i = i.castSucc := by
      apply Fin.succAbove_of_castSucc_lt
      exact Fin.mk_lt_mk.mpr hi
    rw [hs]
    rfl
  · rw [dif_neg hi]
    have hpi : p ≤ i.castSucc := by
      exact Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hi)
    have hs : p.succAbove i = i.succ := by
      exact Fin.succAbove_of_le_castSucc _ _ hpi
    rw [hs]
    rfl

/-- Contracting a globally skipped coordinate preserves levelwise linearity. -/
theorem linearOnLevels_contractSkipped
    {F : ShapeMap binarySucc}
    (hlin : LinearOnLevels F)
    (t : ℕ) (hskip : F.Skips t) :
    LinearOnLevels (contractSkipped F t hskip) := by
  intro n
  obtain ⟨m, φ, hφ⟩ := hlin n
  let w0 : AtLevel n :=
    ⟨⟨List.replicate n 0⟩, by simp⟩
  obtain ⟨h0, hw0⟩ := hφ w0
  have hmne : m ≠ t := by
    intro hmt
    apply hskip
    refine ⟨w0.1, ?_⟩
    change (F w0.1).bits.length = t
    exact h0.trans hmt
  rcases lt_or_gt_of_ne hmne with hmt | htm
  · refine ⟨m, φ, ?_⟩
    intro w
    obtain ⟨hFw, hw⟩ := hφ w
    have hle : (F w.1).bits.length ≤ t := by
      rw [hFw]
      exact Nat.le_of_lt hmt
    have hcontract :
        contractSkipped F t hskip w.1 = F w.1 := by
      apply BinaryWord.ext
      change (F w.1).bits.eraseIdx t = (F w.1).bits
      exact List.eraseIdx_of_length_le hle
    refine ⟨?_, ?_⟩
    · change (contractSkipped F t hskip w.1).bits.length = m
      rw [hcontract]
      exact hFw
    · simpa [hcontract] using hw
  · have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le t) htm
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt hmpos)
    rcases hk with rfl
    let p : Fin (k + 1) := ⟨t, htm⟩
    let ψ : (Fin n → F2) →ₗ[F2] (Fin k → F2) :=
      (removeNthLinearMap p).comp φ
    refine ⟨k, ψ, ?_⟩
    intro w
    obtain ⟨hFw, hw⟩ := hφ w
    have htFw : t < (F w.1).bits.length := by
      simpa [hFw] using htm
    let Fw : AtLevel (k + 1) := ⟨F w.1, hFw⟩
    let hlen :
        (contractSkipped F t hskip w.1).bits.length = k := by
      change (eraseCoordinate t (F w.1)).bits.length = k
      rw [eraseCoordinate_length]
      simp [htFw, hFw]
    refine ⟨hlen, ?_⟩
    change
      levelEquiv k
          ⟨eraseCoordinate t (F w.1), hlen⟩ =
        ψ (levelEquiv n w)
    calc
      levelEquiv k
          ⟨eraseCoordinate t (F w.1), hlen⟩ =
          removeNthLinearMap p (levelEquiv (k + 1) Fw) := by
        simpa [p, Fw] using
          (levelEquiv_eraseCoordinate p Fw)
      _ = removeNthLinearMap p
            (φ (levelEquiv n w)) := by
          rw [hw]
      _ = ψ (levelEquiv n w) := rfl

end BinaryWord
end SuccessorTree.NonPrecompact
