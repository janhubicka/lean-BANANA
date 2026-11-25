import BANANA.NonPrecompact.FiberGridCoordinates

/-! Canonical row and column fibre equivalences for abstract compatible-atom grids. -/

namespace SuccessorTree.NonPrecompact

/-- Fixing the left coordinate of a compatible-pair grid leaves
exactly the right fibre over its base image. -/
def fiberGridRowSubtypeEquiv
    {X Y Z : Type*} (f : Y → X) (g : Z → X) (b : Y) :
    RightFiber g (f b) ≃
      {p : FiberGrid f g // p.2.1.1 = b} where
  toFun c := ⟨⟨f b, (⟨b, rfl⟩, c)⟩, rfl⟩
  invFun p :=
    ⟨p.1.2.2.1,
      p.1.2.2.2.trans
        (p.1.2.1.2.symm.trans (congrArg f p.2))⟩
  left_inv c := by
    apply Subtype.ext
    rfl
  right_inv p := by
    rcases p with ⟨⟨a, ⟨⟨bb, hb⟩, ⟨cc, hc⟩⟩⟩, heq⟩
    dsimp at heq ⊢
    subst bb
    cases hb
    rfl

/-- Fixing the right coordinate leaves exactly the left fibre. -/
def fiberGridColumnSubtypeEquiv
    {X Y Z : Type*} (f : Y → X) (g : Z → X) (c : Z) :
    LeftFiber f (g c) ≃
      {p : FiberGrid f g // p.2.2.1 = c} where
  toFun b := ⟨⟨g c, (b, ⟨c, rfl⟩)⟩, rfl⟩
  invFun p :=
    ⟨p.1.2.1.1,
      p.1.2.1.2.trans
        (p.1.2.2.2.symm.trans (congrArg g p.2))⟩
  left_inv b := by
    apply Subtype.ext
    rfl
  right_inv p := by
    rcases p with ⟨⟨a, ⟨⟨bb, hb⟩, ⟨cc, hc⟩⟩⟩, heq⟩
    dsimp at heq ⊢
    subst cc
    cases hc
    rfl

end SuccessorTree.NonPrecompact
