import BANANA.NonPrecompact.LinearBinaryContraction
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi

/-!
# M2 for the linear binary successor monoid

Let t be the last target level below the image of source level n and suppose
that t is skipped.  Contract t from the shape map.  On level n this gives an
injective linear map psi into F₂^t.  Choose a linear left inverse of psi and
use it to extend the deleted coordinate of the original level-n action to a
linear functional on all of F₂^t.  Reinserting this functional recovers the
original map through source level n.

This is the finite-dimensional linear-algebra argument behind the
manuscript's statement that insertion/removal of prescribed linear
coordinates preserves the allowed rules.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

/-- Pointwise form of a chosen linear left inverse. -/
private theorem leftInverse_apply
    {V W : Type*}
    [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W]
    (f : V →ₗ[F2] W) (g : W →ₗ[F2] V)
    (h : g.comp f = LinearMap.id)
    (x : V) :
    g (f x) = x := by
  have hx := LinearMap.congr_fun h x
  simpa using hx

/-- M2 for levelwise-linear shape maps of the binary prefix tree. -/
theorem linearOnLevels_m2
    (n : ℕ) (F : ShapeMap binarySucc)
    (hlin : LinearOnLevels F)
    (a : BinaryWord) (ha : LevelTree.lev a = n)
    (hpos : 0 < LevelTree.lev (F a))
    (hskip :
      F.Skips (LevelTree.lev (F a) - 1)) :
    ∃ F1 F2 : ShapeMap binarySucc,
      LinearOnLevels F1 ∧
      LinearOnLevels F2 ∧
      F2.SkipsOnly (LevelTree.lev (F a) - 1) ∧
      ∀ x : BinaryWord, LevelTree.lev x ≤ n →
        F2 (F1 x) = F x := by
  let t : ℕ := LevelTree.lev (F a) - 1
  have hFa : LevelTree.lev (F a) = t + 1 := by
    dsimp [t]
    omega

  let F1 : ShapeMap binarySucc :=
    contractSkipped F t hskip
  have hlin1 : LinearOnLevels F1 :=
    linearOnLevels_contractSkipped hlin t hskip

  obtain ⟨m, φ, hφ⟩ := hlin n
  let aN : AtLevel n := ⟨a, ha⟩
  obtain ⟨hFaM, hφa⟩ := hφ aN
  have hm : m = t + 1 := by
    calc
      m = (F a).bits.length := hFaM.symm
      _ = t + 1 := hFa
  rcases hm with rfl

  obtain ⟨m1, ψ, hψ⟩ := hlin1 n
  obtain ⟨hF1aM, hψa⟩ := hψ aN
  have htltFa : t < (F a).bits.length := by
    change t < LevelTree.lev (F a)
    rw [hFa]
    omega
  have hF1aLen : (F1 a).bits.length = t := by
    change (eraseCoordinate t (F a)).bits.length = t
    rw [eraseCoordinate_length, if_pos htltFa]
    change (F a).bits.length = t + 1 at hFa
    rw [hFa]
    omega
  have hm1 : m1 = t := by
    exact hF1aM.symm.trans hF1aLen
  rcases hm1 with rfl

  have hψinj : Function.Injective ψ :=
    levelWitness_injective F1 ψ hψ
  obtain ⟨L, hL⟩ :=
    ψ.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr hψinj)

  let p : Fin (t + 1) := Fin.last t
  let e : LinearBoringRule t :=
    (LinearMap.proj p).comp (φ.comp L)
  let H2 : ShapeMap binarySucc :=
    insertLinearCoordinateShapeMap t e

  refine ⟨F1, H2, hlin1,
    linearOnLevels_insertLinearCoordinateShapeMap t e,
    ?_, ?_⟩
  · simpa [H2, t] using
      insertLinearCoordinateShapeMap_skipsOnly t e
  · intro x hx
    by_cases hxn : LevelTree.lev x = n
    · let xN : AtLevel n := ⟨x, hxn⟩
      obtain ⟨hFx, hφx⟩ := hφ xN
      obtain ⟨hF1x, hψx⟩ := hψ xN
      have hFx' : (F x).bits.length = t + 1 := hFx
      have hF1x' : (F1 x).bits.length = t := hF1x
      let F1xT : AtLevel t := ⟨F1 x, hF1x'⟩
      let v : Fin n → F2 := levelEquiv n xN
      have hLψ : L (ψ v) = v :=
        leftInverse_apply ψ L hL v
      have hscalar :
          e (prefixCoords (F1 x) t (by omega)) =
            (F x).bits[t] := by
        have hpref :
            prefixCoords (F1 x) t (by omega) =
              levelEquiv t F1xT := by
          rfl
        rw [hpref, hψx]
        change (φ (L (ψ v))) p = (F x).bits[t]
        rw [hLψ]
        have hcoord := congrFun hφx p
        change (F x).bits[p.1] = (φ v) p at hcoord
        simpa [p] using hcoord.symm

      change insertLinearCoordinate t e (F1 x) = F x
      have htF1 : t ≤ (F1 x).bits.length := by
        rw [hF1x']
      apply BinaryWord.ext
      change (insertLinearCoordinate t e (F1 x)).bits = (F x).bits
      rw [insertLinearCoordinate_of_le t e (F1 x) htF1]
      rw [hscalar]
      change
        ((F x).bits.eraseIdx t).insertIdx t (F x).bits[t] =
          (F x).bits
      exact List.insertIdx_eraseIdx_getElem (by omega)
    · have hxlt : LevelTree.lev x < n := by omega
      have hFlt :
          LevelTree.lev (F x) < LevelTree.lev (F a) :=
        F.level_lt_of_level_lt (by simpa [ha] using hxlt)
      have hFxNe : LevelTree.lev (F x) ≠ t := by
        intro heq
        exact hskip ⟨x, heq⟩
      have hFxt : LevelTree.lev (F x) < t := by
        rw [hFa] at hFlt
        omega
      have hF1eq : F1 x = F x := by
        apply BinaryWord.ext
        change (F x).bits.eraseIdx t = (F x).bits
        apply List.eraseIdx_of_length_le
        exact Nat.le_of_lt hFxt
      change
        insertLinearCoordinate t e
            (contractSkipped F t hskip x) =
          F x
      rw [show contractSkipped F t hskip x = F x from hF1eq]
      exact insertLinearCoordinate_of_lt t e (F x)
        (by exact hFxt)

end BinaryWord
end SuccessorTree.NonPrecompact
