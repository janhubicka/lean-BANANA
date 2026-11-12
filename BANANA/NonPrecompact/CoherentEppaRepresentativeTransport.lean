import BANANA.NonPrecompact.CoherentConjugation
import Mathlib.Algebra.Group.Action.Defs

/-!
# Representative transport: extension on the selected copies

This is the action-theoretic part of the finite representative argument for
coherent EPPA.  A homomorphism rho of representative automorphisms into the
ambient group acts correctly on a distinguished representative copy.  The
chosen conjugators carry this copy to its selected copies.

Conjugation therefore extends the prescribed representative action at
each selected copy, on both sorts.  Identity, inverse and composition are
already proved independently in CoherentConjugation.

This statement does NOT select representatives of finite BANANA
substructures, construct their pairing-preserving automorphism group or
derive the required group homomorphism from CoherentEppaPackage.  Those
are necessary for a class-wide coherent-EPPA theorem.
-/

namespace SuccessorTree.NonPrecompact

/-- Conjugated transport acts on a selected representative copy as the
original representative automorphism does on its abstract carrier. -/
theorem conjugatedTransport_representative_smul
    {G H O X R : Type*}
    [Group G] [Group H]
    [MulAction G X] [MulAction H R]
    (rho : H →* G) (g : O → G) (j : R → X)
    (hj : ∀ (h : H) (x : R), rho h • j x = j (h • x))
    (U V : O) (h : H) (x : R) :
    conjugatedTransport rho g U V h • (g U • j x) =
      g V • j (h • x) := by
  calc
    conjugatedTransport rho g U V h • (g U • j x) =
        (g V * rho h) • j x := by
      simp [conjugatedTransport, mul_smul]
    _ = g V • j (h • x) := by
      rw [mul_smul, hj h x]

/-- Extension on the left and right sorts of selected copies.  The
conditions hsrcL/hsrcR express that one and the same ambient conjugator
extends the chosen representative identification on BOTH sorts. -/
theorem conjugatedTransport_extends_two_sorts
    {G H O X Y R S : Type*}
    [Group G] [Group H]
    [MulAction G X] [MulAction G Y]
    [MulAction H R] [MulAction H S]
    (rho : H →* G) (g : O → G)
    (jL : R → X) (jR : S → Y)
    (srcL : O → R → X) (srcR : O → S → Y)
    (hsrcL : ∀ (U : O) (x : R), srcL U x = g U • jL x)
    (hsrcR : ∀ (U : O) (y : S), srcR U y = g U • jR y)
    (hρL : ∀ (h : H) (x : R), rho h • jL x = jL (h • x))
    (hρR : ∀ (h : H) (y : S), rho h • jR y = jR (h • y))
    (U V : O) (h : H) :
    (∀ x : R,
      conjugatedTransport rho g U V h • srcL U x =
        srcL V (h • x)) ∧
    (∀ y : S,
      conjugatedTransport rho g U V h • srcR U y =
        srcR V (h • y)) := by
  constructor
  · intro x
    rw [hsrcL U x, hsrcL V (h • x)]
    exact conjugatedTransport_representative_smul
      rho g jL hρL U V h x
  · intro y
    rw [hsrcR U y, hsrcR V (h • y)]
    exact conjugatedTransport_representative_smul
      rho g jR hρR U V h y

end SuccessorTree.NonPrecompact
