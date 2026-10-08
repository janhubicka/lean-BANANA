import BANANA.NonPrecompact.LinearBinarySMTree
import SuccessorTree.ShapeFiniteCorollaries

/-!
# Exact coordinates in the binary linear successor tree

For every source dimension `a` and terminal dimension `D ≥ a`,
repeated zero-coordinate insertions give an exact finite approximation
of the required width and terminal level.  This proves the
`coordinate_nonempty` requirement in the successor-to-GLR bridge,
including the zero-dimensional boundary.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

/-- Insert a zero-valued coordinate at the chosen cut, as an element of the
linear binary distinguished monoid. -/
def zeroInsertion (a : ℕ) :
    SMTree.MMap linearBinarySMTree :=
  ⟨insertLinearCoordinateShapeMap a (0 : LinearBoringRule a),
   linearOnLevels_insertLinearCoordinateShapeMap a 0⟩

/-- Repeat the same zero-coordinate insertion. -/
def zeroPaddingMap (a : ℕ) : ℕ → SMTree.MMap linearBinarySMTree
  | 0 => SMTree.MMap.id linearBinarySMTree
  | k + 1 =>
      SMTree.MMap.comp linearBinarySMTree
        (zeroInsertion a) (zeroPaddingMap a k)

theorem zeroInsertion_levelMap
    (a n : ℕ) (h : a ≤ n) :
    linearBinarySMTree.levelMap (zeroInsertion a).map n = n + 1 := by
  let w : BinaryWord := ⟨List.replicate n 0⟩
  have hw : LevelTree.lev w = n := by
    change (List.replicate n (0 : F2)).length = n
    simp
  have hℓ :=
    linearBinarySMTree.levelMap_eq
      (zeroInsertion a).map (a := w)
  rw [hw] at hℓ
  rw [hℓ]
  have hins :=
    insertLinearCoordinateShapeMap_level
      a (0 : LinearBoringRule a) w
  change
    LevelTree.lev (zeroInsertion a w) =
      (if LevelTree.lev w < a then LevelTree.lev w
        else LevelTree.lev w + 1) at hins
  rw [hw] at hins
  simp [Nat.not_lt.mpr h] at hins
  exact hins

theorem zeroPaddingMap_levelMap
    (a : ℕ) :
    ∀ k : ℕ,
      linearBinarySMTree.levelMap (zeroPaddingMap a k).map a =
        a + k := by
  intro k
  induction k with
  | zero =>
      simpa [zeroPaddingMap] using
        SMTree.MMap.levelMap_id linearBinarySMTree a
  | succ k ih =>
      rw [zeroPaddingMap, SMTree.MMap.levelMap_comp, ih]
      rw [zeroInsertion_levelMap a (a + k) (Nat.le_add_right a k)]
      omega

/-- A level-`a` exact finite approximation ending at target level `D`.
The source-space dimension is `a`. -/
noncomputable def zeroPaddingExact
    (a D : ℕ) (h : a ≤ D) :
    SMTree.AM.At linearBinarySMTree 0 (a + 1) D := by
  let k := D - a
  let F := zeroPaddingMap a k
  have hfix : F.FixesBelow linearBinarySMTree 0 := by
    intro x hx
    omega
  let f : SMTree.AM linearBinarySMTree 0 (a + 1) :=
    F.toAM linearBinarySMTree 0 (a + 1) hfix
  refine ⟨f, ?_⟩
  have hterm :=
    SMTree.MMap.toAM_terminalLevel
      linearBinarySMTree F 0 (a + 1) hfix (by omega)
  change f.terminalLevel linearBinarySMTree = D
  rw [hterm]
  have hlast : 0 + (a + 1) - 1 = a := by omega
  rw [hlast, zeroPaddingMap_levelMap]
  dsimp [k]
  omega

/-- The coordinate-nonemptiness field of the GLR representation interface
requires no pivot argument. -/
theorem exactCoordinate_nonempty {a D : ℕ} (haD : a ≤ D) :
    Nonempty
      (SMTree.AM.At linearBinarySMTree 0 (a + 1)
        (0 + (D + 1) - 1)) := by
  have hlast : 0 + (D + 1) - 1 = D := by omega
  rw [hlast]
  exact ⟨zeroPaddingExact a D haD⟩

end BinaryWord
end SuccessorTree.NonPrecompact
