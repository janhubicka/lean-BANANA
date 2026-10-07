import BANANA.NonPrecompact.LinearBinaryRanges
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
  have hGnext :
      LevelTree.lev (G (appendBit x c)) =
        LevelTree.lev (F x) + 1 := by
    calc
      LevelTree.lev (G (appendBit x c)) =
          H.levelMap G.map (n + 1) := by
            simpa [hxnext] using
              (H.levelMap_eq G.map (a := appendBit x c)).symm
      _ = H.levelMap G.map n + 1 :=
        H.canonicalExtension_level_succ F n n le_rfl
      _ = H.levelMap F.map n + 1 := by
        rw [H.canonicalExtension_level_at_prefix F n]
      _ = LevelTree.lev (F x) + 1 := by
        have hFx : H.levelMap F.map n = LevelTree.lev (F x) := by
          simpa only [hx] using (H.levelMap_eq F.map (a := x))
        rw [hFx]
  have hsucc : binarySucc.succ x [] c = some (appendBit x c) := by
    rfl
  obtain ⟨d, hd, hdb⟩ := G.map.weak_succ' hsucc
  have hcover : G x ⋖ d :=
    binarySucc.covBy_of_succ_eq_some hd
  have hdlevel :
      LevelTree.lev d = LevelTree.lev (G x) + 1 :=
    LevelTree.covBy_level_eq hcover
  have hsame :
      LevelTree.lev d = LevelTree.lev (G (appendBit x c)) := by
    rw [hdlevel, hGx, hGnext]
  have hd_eq : d = G (appendBit x c) :=
    LevelTree.same_level_of_le hdb hsame
  have hlabel : d = appendBit (G x) c := by
    change (some (appendBit (G x) c) : Option BinaryWord) =
      some d at hd
    exact (Option.some.inj hd).symm
  calc
    G (appendBit x c) = d := hd_eq.symm
    _ = appendBit (G x) c := hlabel
    _ = appendBit (F x) c := congrArg (fun w => appendBit w c) hGx

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

end BinaryWord
end SuccessorTree.NonPrecompact
