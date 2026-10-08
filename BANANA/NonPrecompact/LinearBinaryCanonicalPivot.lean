import BANANA.NonPrecompact.LinearBinaryRanges
import BANANA.NonPrecompact.BinarySubspaceStep
import SuccessorTree.Canonical

/-!
# Immediate pivot extension from the canonical successor extension

The finite successor tree theorem supplies a canonical extension which
closes every gap after the prescribed source cut.  In the binary prefix
tree a source bit is the label of its incoming successor edge.  Therefore,
immediately after the cut, the canonical extension appends precisely the
same bit to the target word.

This is the exact local step needed when the last ambient coordinate is
independent on the represented subspace: the extra source coordinate is a
new free pivot, rather than a boring coordinate.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

/-- At a fixed level, appending one bit to a binary word is
the standard `Fin.snoc` extension of its coordinate vector. -/
theorem levelEquiv_appendBit
    (d : ℕ) (w : AtLevel d) (c : F2) :
    let hlen : (appendBit w.1 c).bits.length = d + 1 := by
      simp [appendBit, w.2]
    levelEquiv (d + 1) ⟨appendBit w.1 c, hlen⟩ =
      Fin.snoc (levelEquiv d w) c := by
  intro hlen
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [levelEquiv, appendBit, Fin.snoc_last, w.2]
  · simp [levelEquiv, appendBit, Fin.snoc_castSucc, w.2]

/-- At the first source level beyond its fixed prefix, the canonical
extension maps the labelled binary edge to an actual labelled edge.

The resulting target level is consecutive, so the weak successor
preservation of a shape map is automatically exact. -/
theorem canonicalExtension_appendBit_at_cut
    (F : SMTree.MMap linearBinarySMTree)
    (n : ℕ) (x : BinaryWord) (c : F2)
    (hx : LevelTree.lev x = n) :
    linearBinarySMTree.canonicalExtension F n (appendBit x c) =
      appendBit (F x) c := by
  let H := linearBinarySMTree
  let G : SMTree.MMap H := H.canonicalExtension F n
  have hGx : G x = F x :=
    H.canonicalExtension_agrees F n x (Nat.le_of_eq hx)
  have hxnext : LevelTree.lev (appendBit x c) = n + 1 := by
    change (x.bits ++ [c]).length = n + 1
    simp [show x.bits.length = n from hx]
  have hlevels :
      H.levelMap G.map (LevelTree.lev (appendBit x c)) =
        H.levelMap G.map (LevelTree.lev x) + 1 := by
    rw [hxnext, hx]
    exact H.canonicalExtension_level_succ F n n le_rfl
  have hsucc : binarySucc.succ x [] c = some (appendBit x c) := by
    rfl
  have hsucc' := H.succ_eq_of_consecutive_levels G.map hsucc hlevels
  change
    (some (appendBit (G x) c) : Option BinaryWord) =
      some (G (appendBit x c)) at hsucc'
  calc
    G (appendBit x c) = appendBit (G x) c :=
      (Option.some.inj hsucc').symm
    _ = appendBit (F x) c :=
      congrArg (fun y => appendBit y c) hGx

/-- Canonical continuation raises an exact source dimension and
its terminal target height by one. -/
noncomputable def extendExactWithPivot
    {d N : ℕ}
    (f : SMTree.AM.At linearBinarySMTree 0 (d + 1) N) :
    SMTree.AM.At linearBinarySMTree 0 (d + 2) (N + 1) := by
  let H := linearBinarySMTree
  let F := f.1.representative H
  let G := H.canonicalExtension F d
  have hGfix : G.FixesBelow H 0 := by
    intro x hx
    omega
  let g : SMTree.AM H 0 (d + 2) :=
    G.toAM H 0 (d + 2) hGfix
  refine ⟨g, ?_⟩
  have hterm :=
    SMTree.MMap.toAM_terminalLevel H G 0 (d + 2) hGfix
      (by omega : 0 < 0 + (d + 2))
  change g.terminalLevel H = N + 1
  rw [hterm]
  have hindex : 0 + (d + 2) - 1 = d + 1 := by omega
  rw [hindex]
  rw [H.canonicalExtension_level_succ F d d le_rfl]
  rw [H.canonicalExtension_level_at_prefix F d]
  have hbefore : H.levelMap F.map d = N := by
    have hf : f.1.terminalLevel H = N := f.2
    unfold SMTree.AM.terminalLevel at hf
    have hd : 0 + (d + 1) - 1 = d := by omega
    rwa [hd] at hf
  rw [hbefore]


/-- On the new top source level the representative of the extended
approximation agrees with the canonical total extension. -/
theorem extendExactWithPivot_representative_agrees
    {d N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (d + 1) N)
    (w : AtLevel (d + 1)) :
    ((extendExactWithPivot f).1.representative LinearBinaryH) w.1 =
      (LinearBinaryH.canonicalExtension
        (f.1.representative LinearBinaryH) d) w.1 := by
  let F := f.1.representative LinearBinaryH
  let G := LinearBinaryH.canonicalExtension F d
  have hfix : G.FixesBelow LinearBinaryH 0 := by
    intro x hx
    omega
  change
    ((G.toAM LinearBinaryH 0 (d + 2) hfix).representative
      LinearBinaryH) w.1 = G w.1
  apply SMTree.MMap.toAM_representative_agrees
    LinearBinaryH G 0 (d + 2) hfix
  change w.1.bits.length < 0 + (d + 2)
  omega

/-- The new pivot appears as an independent final bit in the induced
linear map, in the last-coordinate product presentation. -/
theorem extendExactWithPivot_action_append
    {d N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (d + 1) N)
    (w : AtLevel d) (c : F2) :
    lastCoordinateLinearEquiv N
      ((exactLinearModel (extendExactWithPivot f)).map
        (Fin.snoc (levelEquiv d w) c)) =
      ((exactLinearModel f).map (levelEquiv d w), c) := by
  let src : AtLevel (d + 1) :=
    ⟨appendBit w.1 c, by simp [appendBit, w.2]⟩
  let F := f.1.representative LinearBinaryH
  obtain ⟨hG, hactionG⟩ :=
    (exactLinearModel (extendExactWithPivot f)).action src
  obtain ⟨hF, hactionF⟩ :=
    (exactLinearModel f).action w
  have hrep :
      ((extendExactWithPivot f).1.representative
        LinearBinaryH) src.1 = appendBit (F w.1) c := by
    calc
      ((extendExactWithPivot f).1.representative
        LinearBinaryH) src.1 =
          (LinearBinaryH.canonicalExtension F d) src.1 :=
        extendExactWithPivot_representative_agrees f src
      _ = appendBit (F w.1) c :=
        canonicalExtension_appendBit_at_cut F d w.1 c w.2
  have hlen :
      (appendBit (F w.1) c).bits.length = N + 1 := by
    simp [appendBit, hF]
  have hsub :
      (⟨((extendExactWithPivot f).1.representative
            LinearBinaryH) src.1, hG⟩ : AtLevel (N + 1)) =
        (⟨appendBit (F w.1) c, hlen⟩ : AtLevel (N + 1)) :=
    Subtype.ext hrep
  have hsource :
      levelEquiv (d + 1) src = Fin.snoc (levelEquiv d w) c :=
    levelEquiv_appendBit d w c
  have htarget :
      levelEquiv (N + 1) ⟨appendBit (F w.1) c, hlen⟩ =
        Fin.snoc (levelEquiv N ⟨F w.1, hF⟩) c :=
    levelEquiv_appendBit N ⟨F w.1, hF⟩ c
  have hmodel :
      (exactLinearModel (extendExactWithPivot f)).map
        (Fin.snoc (levelEquiv d w) c) =
      Fin.snoc ((exactLinearModel f).map (levelEquiv d w)) c := by
    calc
      (exactLinearModel (extendExactWithPivot f)).map
          (Fin.snoc (levelEquiv d w) c) =
          (exactLinearModel (extendExactWithPivot f)).map
            (levelEquiv (d + 1) src) := by rw [hsource]
      _ = levelEquiv (N + 1)
            ⟨((extendExactWithPivot f).1.representative
                LinearBinaryH) src.1, hG⟩ := hactionG.symm
      _ = levelEquiv (N + 1)
            ⟨appendBit (F w.1) c, hlen⟩ :=
        congrArg (levelEquiv (N + 1)) hsub
      _ = Fin.snoc (levelEquiv N ⟨F w.1, hF⟩) c := htarget
      _ = Fin.snoc ((exactLinearModel f).map (levelEquiv d w)) c := by
        rw [hactionF]
  rw [hmodel]
  simp [lastCoordinateLinearEquiv]

/-- To realise the product of a represented subspace with one new free
coordinate, it suffices that the target subspace has that product
membership condition. Both have dimension `d+1`, so inclusion is enough. -/
theorem extendExactWithPivot_realises_product
    {d N : ℕ}
    (f : SMTree.AM.At LinearBinaryH 0 (d + 1) N)
    (P : FixedSubspace (d + 1) (N + 1))
    (hprod : ∀ z : Fin (N + 1) → F2,
      z ∈ P.1 ↔
        (lastCoordinateLinearEquiv N z).1 ∈ (exactSubspace f).1) :
    exactSubspace (extendExactWithPivot f) = P := by
  apply exactSubspace_eq_of_range_le (extendExactWithPivot f) P
  rintro v ⟨x, rfl⟩
  let u : Fin d → F2 := Fin.init x
  let c : F2 := x (Fin.last d)
  let w : AtLevel d := (levelEquiv d).symm u
  have hwu : levelEquiv d w = u :=
    (levelEquiv d).apply_symm_apply u
  have hxs : Fin.snoc u c = x := by
    exact Fin.snoc_init_self x
  have hcoord := extendExactWithPivot_action_append f w c
  rw [hwu, hxs] at hcoord
  apply (hprod _).2
  rw [hcoord]
  exact ⟨u, rfl⟩

end BinaryWord
end SuccessorTree.NonPrecompact
