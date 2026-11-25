import BANANA.NonPrecompact.ParityStarMatrix
import BANANA.NonPrecompact.FiberProductStrong
import BANANA.NonPrecompact.FiberGridCoordinates

/-!
# Parity amalgamation on fibre-product atom grids

This file packages the finite atom-grid construction behind strong
amalgamation for pre-BANANA.

For surjections f : B → A and g : C → A, the amalgam atoms are triples
(a,b,c) with f(b)=a=g(c).  On each fibre rectangle we put the explicit
star matrix with the prescribed B-row and C-column F₂ marks.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- Marking on the fibre-product atom grid obtained by putting the explicit
star matrix on each source-atom rectangle. -/
noncomputable def fiberGridMark
    {A B C : Type*}
    [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (f : B → A) (g : C → A)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (markB : B → F2) (markC : C → F2)
    (p : FiberGrid f g) : F2 :=
  parityStarMatrix
    (fun b : LeftFiber f p.1 => markB b.1)
    (fun c : RightFiber g p.1 => markC c.1)
    (leftFiberBase f hf p.1)
    (rightFiberBase g hg p.1)
    p.2.1 p.2.2

/-- Every B-atom row of the fibre-product grid has the prescribed B mark. -/
theorem sum_fiberGridMark_right
    {A B C : Type*}
    [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (f : B → A) (g : C → A)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (markB : B → F2) (markC : C → F2)
    (b : B) :
    (∑ c : RightFiber g (f b),
      fiberGridMark f g hf hg markB markC
        ⟨f b, (⟨b, rfl⟩, c)⟩) =
      markB b := by
  simpa [fiberGridMark] using
    sum_row_parityStarMatrix
      (fun b' : LeftFiber f (f b) => markB b'.1)
      (fun c' : RightFiber g (f b) => markC c'.1)
      (leftFiberBase f hf (f b))
      (rightFiberBase g hg (f b))
      (⟨b, rfl⟩ : LeftFiber f (f b))

/-- If the B- and C-fibre totals agree over every base atom, then every
C-atom column of the fibre-product grid has the prescribed C mark. -/
theorem sum_fiberGridMark_left
    {A B C : Type*}
    [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (f : B → A) (g : C → A)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g)
    (markB : B → F2) (markC : C → F2)
    (htotal :
      ∀ a : A,
        (∑ b : LeftFiber f a, markB b.1) =
          ∑ c : RightFiber g a, markC c.1)
    (c : C) :
    (∑ b : LeftFiber f (g c),
      fiberGridMark f g hf hg markB markC
        ⟨g c, (b, ⟨c, rfl⟩)⟩) =
      markC c := by
  simpa [fiberGridMark] using
    sum_col_parityStarMatrix
      (fun b' : LeftFiber f (g c) => markB b'.1)
      (fun c' : RightFiber g (g c) => markC c'.1)
      (leftFiberBase f hf (g c))
      (rightFiberBase g hg (g c))
      (htotal (g c))
      (⟨c, rfl⟩ : RightFiber g (g c))

end SuccessorTree.NonPrecompact
