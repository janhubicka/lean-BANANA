import BANANA.NonPrecompact.FolkmanCofinalBridgeChain

/-!
# From an exhaustive coherent finite bridge chain to a global automorphism

This adapts the finite-bridge limit argument already used in the
pre-BANANA formalisation. Unlike the pre-BANANA case, each bridge
has two ring sorts and a bilinear cross-pairing; both sorts may
lack ambient units.

The chain provides coherence, common refinements of finite
representatives and two-sided exhaustion. We show that its two
forward maps are bijective, preserve both ring operations and
preserve the entire F₂ pairing. This packages an actual global
pairing automorphism, not a finite partial isomorphism.

Construction of the exhaustive chain from the finite extension
property remains a separate task. This file is source-only pending
the pinned local Lean build and transitive axiom audit.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

namespace FolkmanCofinalBridgeChain

variable {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
variable {β : L → R → F2}

/-- Coherence in both directions makes the global left map injective. -/
theorem forwardLeft_injective (C : FolkmanCofinalBridgeChain L R β) :
    Function.Injective C.forwardLeft := by
  classical
  intro x y hxy
  let wx := C.chooseLeft x
  let wy := C.chooseLeft y
  have hx : C.sourceLeft wx.1 wx.2 = x := C.chooseLeft_spec x
  have hy : C.sourceLeft wy.1 wy.2 = y := C.chooseLeft_spec y
  have ht : C.targetLeft wx.1 wx.2 = C.targetLeft wy.1 wy.2 := by
    change C.targetLeft wx.1 wx.2 = C.targetLeft wy.1 wy.2 at hxy
    exact hxy
  have hs := C.left_backward_coherent wx.1 wy.1 wx.2 wy.2 ht
  exact hx.symm.trans (hs.trans hy)

/-- Exhaustion of target-stage images makes the global left map onto. -/
theorem forwardLeft_surjective (C : FolkmanCofinalBridgeChain L R β) :
    Function.Surjective C.forwardLeft := by
  intro y
  obtain ⟨n, a, ha⟩ := C.targetLeft_exhaustive y
  exact ⟨C.sourceLeft n a, (C.forwardLeft_on_stage n a).trans ha⟩

/-- Identical injectivity result for the right ring sort. -/
theorem forwardRight_injective (C : FolkmanCofinalBridgeChain L R β) :
    Function.Injective C.forwardRight := by
  classical
  intro x y hxy
  let wx := C.chooseRight x
  let wy := C.chooseRight y
  have hx : C.sourceRight wx.1 wx.2 = x := C.chooseRight_spec x
  have hy : C.sourceRight wy.1 wy.2 = y := C.chooseRight_spec y
  have ht : C.targetRight wx.1 wx.2 = C.targetRight wy.1 wy.2 := by
    change C.targetRight wx.1 wx.2 = C.targetRight wy.1 wy.2 at hxy
    exact hxy
  have hs := C.right_backward_coherent wx.1 wy.1 wx.2 wy.2 ht
  exact hx.symm.trans (hs.trans hy)

/-- Exhaustion of target images on the right ring sort. -/
theorem forwardRight_surjective (C : FolkmanCofinalBridgeChain L R β) :
    Function.Surjective C.forwardRight := by
  intro y
  obtain ⟨n, a, ha⟩ := C.targetRight_exhaustive y
  exact ⟨C.sourceRight n a, (C.forwardRight_on_stage n a).trans ha⟩

/-- The common-stage hypothesis transfers ring addition to the
coherent forward map on the left sort. -/
theorem forwardLeft_add (C : FolkmanCofinalBridgeChain L R β)
    (x y : L) :
    C.forwardLeft (x + y) = C.forwardLeft x + C.forwardLeft y := by
  classical
  let wx := C.chooseLeft x
  let wy := C.chooseLeft y
  obtain ⟨k, a, b, ha, hfa, hb, hfb⟩ :=
    C.commonLeft wx.1 wy.1 wx.2 wy.2
  have hx : C.sourceLeft k a = x :=
    ha.trans (C.chooseLeft_spec x)
  have hy : C.sourceLeft k b = y :=
    hb.trans (C.chooseLeft_spec y)
  have hfx : C.forwardLeft x = C.targetLeft k a := by
    change C.targetLeft wx.1 wx.2 = C.targetLeft k a
    exact hfa.symm
  have hfy : C.forwardLeft y = C.targetLeft k b := by
    change C.targetLeft wy.1 wy.2 = C.targetLeft k b
    exact hfb.symm
  have hxy : C.sourceLeft k (a + b) = x + y := by
    rw [map_add, hx, hy]
  calc
    C.forwardLeft (x + y) =
        C.forwardLeft (C.sourceLeft k (a + b)) :=
      congrArg C.forwardLeft hxy.symm
    _ = C.targetLeft k (a + b) := C.forwardLeft_on_stage k (a + b)
    _ = C.targetLeft k a + C.targetLeft k b := map_add _ _ _
    _ = C.forwardLeft x + C.forwardLeft y := by rw [hfx, hfy]

/-- The same common-stage argument transfers multiplication on
left original ring elements, not merely on the atom code. -/
theorem forwardLeft_mul (C : FolkmanCofinalBridgeChain L R β)
    (x y : L) :
    C.forwardLeft (x * y) = C.forwardLeft x * C.forwardLeft y := by
  classical
  let wx := C.chooseLeft x
  let wy := C.chooseLeft y
  obtain ⟨k, a, b, ha, hfa, hb, hfb⟩ :=
    C.commonLeft wx.1 wy.1 wx.2 wy.2
  have hx : C.sourceLeft k a = x :=
    ha.trans (C.chooseLeft_spec x)
  have hy : C.sourceLeft k b = y :=
    hb.trans (C.chooseLeft_spec y)
  have hfx : C.forwardLeft x = C.targetLeft k a := by
    change C.targetLeft wx.1 wx.2 = C.targetLeft k a
    exact hfa.symm
  have hfy : C.forwardLeft y = C.targetLeft k b := by
    change C.targetLeft wy.1 wy.2 = C.targetLeft k b
    exact hfb.symm
  have hxy : C.sourceLeft k (a * b) = x * y := by
    rw [map_mul, hx, hy]
  calc
    C.forwardLeft (x * y) =
        C.forwardLeft (C.sourceLeft k (a * b)) :=
      congrArg C.forwardLeft hxy.symm
    _ = C.targetLeft k (a * b) := C.forwardLeft_on_stage k (a * b)
    _ = C.targetLeft k a * C.targetLeft k b := map_mul _ _ _
    _ = C.forwardLeft x * C.forwardLeft y := by rw [hfx, hfy]

/-- Right ring addition is preserved, using the same finite-stage
coherence condition as for the left sort. -/
theorem forwardRight_add (C : FolkmanCofinalBridgeChain L R β)
    (x y : R) :
    C.forwardRight (x + y) = C.forwardRight x + C.forwardRight y := by
  classical
  let wx := C.chooseRight x
  let wy := C.chooseRight y
  obtain ⟨k, a, b, ha, hfa, hb, hfb⟩ :=
    C.commonRight wx.1 wy.1 wx.2 wy.2
  have hx : C.sourceRight k a = x :=
    ha.trans (C.chooseRight_spec x)
  have hy : C.sourceRight k b = y :=
    hb.trans (C.chooseRight_spec y)
  have hfx : C.forwardRight x = C.targetRight k a := by
    change C.targetRight wx.1 wx.2 = C.targetRight k a
    exact hfa.symm
  have hfy : C.forwardRight y = C.targetRight k b := by
    change C.targetRight wy.1 wy.2 = C.targetRight k b
    exact hfb.symm
  have hxy : C.sourceRight k (a + b) = x + y := by
    rw [map_add, hx, hy]
  calc
    C.forwardRight (x + y) =
        C.forwardRight (C.sourceRight k (a + b)) :=
      congrArg C.forwardRight hxy.symm
    _ = C.targetRight k (a + b) := C.forwardRight_on_stage k (a + b)
    _ = C.targetRight k a + C.targetRight k b := map_add _ _ _
    _ = C.forwardRight x + C.forwardRight y := by rw [hfx, hfy]

/-- Right ring multiplication is preserved without an ambient unit. -/
theorem forwardRight_mul (C : FolkmanCofinalBridgeChain L R β)
    (x y : R) :
    C.forwardRight (x * y) = C.forwardRight x * C.forwardRight y := by
  classical
  let wx := C.chooseRight x
  let wy := C.chooseRight y
  obtain ⟨k, a, b, ha, hfa, hb, hfb⟩ :=
    C.commonRight wx.1 wy.1 wx.2 wy.2
  have hx : C.sourceRight k a = x :=
    ha.trans (C.chooseRight_spec x)
  have hy : C.sourceRight k b = y :=
    hb.trans (C.chooseRight_spec y)
  have hfx : C.forwardRight x = C.targetRight k a := by
    change C.targetRight wx.1 wx.2 = C.targetRight k a
    exact hfa.symm
  have hfy : C.forwardRight y = C.targetRight k b := by
    change C.targetRight wy.1 wy.2 = C.targetRight k b
    exact hfb.symm
  have hxy : C.sourceRight k (a * b) = x * y := by
    rw [map_mul, hx, hy]
  calc
    C.forwardRight (x * y) =
        C.forwardRight (C.sourceRight k (a * b)) :=
      congrArg C.forwardRight hxy.symm
    _ = C.targetRight k (a * b) := C.forwardRight_on_stage k (a * b)
    _ = C.targetRight k a * C.targetRight k b := map_mul _ _ _
    _ = C.forwardRight x * C.forwardRight y := by rw [hfx, hfy]

/-- The two coherent forward maps preserve the *original* ambient
F₂ pairing on every element of the full left/right sorts. -/
theorem forward_preserves_pairing (C : FolkmanCofinalBridgeChain L R β)
    (x : L) (y : R) :
    β (C.forwardLeft x) (C.forwardRight y) = β x y := by
  classical
  let wx := C.chooseLeft x
  let wy := C.chooseRight y
  obtain ⟨k, a, b, ha, hfa, hb, hfb⟩ :=
    C.commonPair wx.1 wy.1 wx.2 wy.2
  have hx : C.sourceLeft k a = x :=
    ha.trans (C.chooseLeft_spec x)
  have hy : C.sourceRight k b = y :=
    hb.trans (C.chooseRight_spec y)
  have hfx : C.forwardLeft x = C.targetLeft k a := by
    change C.targetLeft wx.1 wx.2 = C.targetLeft k a
    exact hfa.symm
  have hfy : C.forwardRight y = C.targetRight k b := by
    change C.targetRight wy.1 wy.2 = C.targetRight k b
    exact hfb.symm
  calc
    β (C.forwardLeft x) (C.forwardRight y) =
        β (C.targetLeft k a) (C.targetRight k b) := by rw [hfx, hfy]
    _ = β (C.sourceLeft k a) (C.sourceRight k b) :=
      (C.stage_pairing k a b).symm
    _ = β x y := by rw [hx, hy]

/-- The cofinal bridge chain gives a global non-unital ring
equivalence of the original left sort. -/
noncomputable def leftRingEquiv (C : FolkmanCofinalBridgeChain L R β) :
    L ≃+* L :=
  { Equiv.ofBijective C.forwardLeft
        ⟨C.forwardLeft_injective, C.forwardLeft_surjective⟩ with
    map_add' := C.forwardLeft_add
    map_mul' := C.forwardLeft_mul }

/-- The corresponding global non-unital equivalence of the
original right sort. -/
noncomputable def rightRingEquiv (C : FolkmanCofinalBridgeChain L R β) :
    R ≃+* R :=
  { Equiv.ofBijective C.forwardRight
        ⟨C.forwardRight_injective, C.forwardRight_surjective⟩ with
    map_add' := C.forwardRight_add
    map_mul' := C.forwardRight_mul }

/-- Every exhaustive coherent finite bridge chain gives a genuine
global pairing-preserving automorphism of the original two-sorted
non-unital Folkman structure. No global unit or external group
structure is needed. -/
noncomputable def globalAutomorphism
    (C : FolkmanCofinalBridgeChain L R β) :
    FolkmanGlobalPairAutomorphism L R β where
  left := C.leftRingEquiv
  right := C.rightRingEquiv
  preserves_pairing := C.forward_preserves_pairing

end FolkmanCofinalBridgeChain
end SuccessorTree.NonPrecompact
