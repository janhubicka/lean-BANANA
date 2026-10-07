import BANANA.NonPrecompact.LinearBinaryRanges
import SuccessorTree.ShapeFiniteCorollaries

/-!
# Composition of exact binary successor ranges

The finite successor theorem composes exact approximations.  On a fixed
source level the representative of that finite composite agrees with
literal composition of the two chosen total maps.  Since the linear
binary monoid is linear on every level, the induced linear maps compose.

Consequently the range of the exact composite is the image of the inner
range under the outer level map.  This is one of the two necessary
ingredients for the concrete binary-GLR encoding.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

open Module

/-- On exact finite linear binary approximations, the induced level
linear map respects finite successor composition. -/
theorem exactLinearModel_comp
    {a D N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (D + 1) N)
    (g : SMTree.AM.At LinearBinaryH 0 (a + 1) D) :
    (exactLinearModel
      (SMTree.exactComp LinearBinaryH
        (by omega : 0 < D + 1)
        (by omega : 0 < a + 1)
        f g)).map =
      (exactLinearModel f).map.comp (exactLinearModel g).map := by
  apply LinearMap.ext
  intro x
  let w : AtLevel a := (levelEquiv a).symm x
  have hw : levelEquiv a w = x :=
    (levelEquiv a).apply_symm_apply x

  let F := f.1.representative LinearBinaryH
  let G := g.1.representative LinearBinaryH
  let fg : SMTree.AM.At LinearBinaryH 0 (a + 1) N :=
    SMTree.exactComp LinearBinaryH
      (by omega : 0 < D + 1)
      (by omega : 0 < a + 1)
      f g
  let FG := fg.1.representative LinearBinaryH

  obtain ⟨hGw, hg⟩ :=
    (exactLinearModel g).action w
  let Gw : AtLevel D := ⟨G w.1, hGw⟩
  obtain ⟨hFGw, hfg⟩ :=
    (exactLinearModel fg).action w
  obtain ⟨hFwg, hf⟩ :=
    (exactLinearModel f).action Gw

  have hrep : FG w.1 = F (G w.1) := by
    change
      (SMTree.finiteShapeComp LinearBinaryH f.1 g.1).representative
          LinearBinaryH w.1 =
        F (G w.1)
    exact SMTree.finiteShapeComp_representative_agrees
      LinearBinaryH f.1 g.1 w.1 (by
        change w.1.bits.length < 0 + (a + 1)
        omega)

  have hsub :
      (⟨FG w.1, hFGw⟩ : AtLevel N) =
        (⟨F (G w.1), hFwg⟩ : AtLevel N) :=
    Subtype.ext hrep

  change
    (exactLinearModel fg).map x =
      (exactLinearModel f).map ((exactLinearModel g).map x)
  calc
    (exactLinearModel fg).map x =
        (exactLinearModel fg).map (levelEquiv a w) := by
      rw [hw]
    _ = levelEquiv N ⟨FG w.1, hFGw⟩ := hfg.symm
    _ = levelEquiv N ⟨F (G w.1), hFwg⟩ :=
      congrArg (levelEquiv N) hsub
    _ = (exactLinearModel f).map (levelEquiv D Gw) := hf
    _ = (exactLinearModel f).map
          ((exactLinearModel g).map x) := by
      rw [hg, hw]

/-- The exact-composition range is the image of the inner range
under the outer levelwise linear map. -/
theorem exactSubspace_comp
    {a D N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (D + 1) N)
    (g : SMTree.AM.At LinearBinaryH 0 (a + 1) D) :
    (exactSubspace
      (SMTree.exactComp LinearBinaryH
        (by omega : 0 < D + 1)
        (by omega : 0 < a + 1)
        f g)).1 =
      Submodule.map (exactLinearModel f).map (exactSubspace g).1 := by
  change
    LinearMap.range
      (exactLinearModel
        (SMTree.exactComp LinearBinaryH
          (by omega : 0 < D + 1)
          (by omega : 0 < a + 1)
          f g)).map =
      Submodule.map (exactLinearModel f).map
        (LinearMap.range (exactLinearModel g).map)
  rw [exactLinearModel_comp f g, LinearMap.range_comp]

end BinaryWord
end SuccessorTree.NonPrecompact
