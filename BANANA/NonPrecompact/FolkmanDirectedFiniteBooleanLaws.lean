import BANANA.NonPrecompact.FolkmanDirectedFiniteLocalFiniteness

/-!
# Boolean-ring identities in a directed non-unital Folkman union

A directed atlas covers each pair of original elements by a finite
powerset Boolean ring embedded in the ambient non-unital ring. Thus
the ambient ring satisfies characteristic two, idempotence and
commutativity, even though it need not possess a multiplicative unit.

The identities are deduced from finite stage maps, not stipulated
as additional global axioms. Local finiteness is supplied separately
by FolkmanDirectedFiniteLocalFiniteness.

This does not construct or assert a Fraisse limit.
-/

namespace SuccessorTree.NonPrecompact

/-- A homomorphism from a Boolean ring into a non-unital ring
transfers Boolean identities to every pair of elements of its range.
In particular, no target multiplicative identity is involved. -/
theorem booleanLaws_on_nonunitalRingHom_range
    {S T : Type*} [BooleanRing S] [NonUnitalRing T]
    (f : S →ₙ+* T) (a b : S) :
    (f a + f a = 0) ∧
    (f a * f a = f a) ∧
    (f a * f b = f b * f a) := by
  constructor
  · calc
      f a + f a = f (a + a) := (map_add f a a).symm
      _ = f 0 := by rw [BooleanRing.add_self]
      _ = 0 := map_zero f
  constructor
  · calc
      f a * f a = f (a * a) := (map_mul f a a).symm
      _ = f a := by rw [BooleanRing.mul_self]
  · calc
      f a * f b = f (a * b) := (map_mul f a b).symm
      _ = f (b * a) := by rw [mul_comm]
      _ = f b * f a := map_mul f b a

/-- The left original ring of any exhaustive Folkman finite-stage
atlas satisfies the Boolean identities, although its global unit
need not exist. This is an assertion about every pair of ambient
elements, not only those within a previously selected stage. -/
theorem FolkmanDirectedFiniteStageAtlas.left_booleanLaws
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (x y : L) :
    (x + x = 0) ∧ (x * x = x) ∧ (x * y = y * x) := by
  classical
  let xs : Fin 2 → L := fun i => if i = 0 then x else y
  let ys : Fin 0 → R := fun j => Fin.elim0 j
  let w : FolkmanFiniteTupleStageWitness (β := β) xs ys :=
    Classical.choice (A.covers 2 0 xs ys)
  let a : AsBoolRing (Finset (Fin w.stage.atom.leftCount)) :=
    toBoolRing (w.leftTuple 0)
  let b : AsBoolRing (Finset (Fin w.stage.atom.leftCount)) :=
    toBoolRing (w.leftTuple 1)
  have ha : w.stage.left a = x := by
    simpa [xs, a] using w.left_spec 0
  have hb : w.stage.left b = y := by
    simpa [xs, b] using w.left_spec 1
  simpa only [ha, hb] using
    (booleanLaws_on_nonunitalRingHom_range w.stage.left a b)

/-- The same identities hold on the right original sort,
independently of any multiplicative identity on that sort. -/
theorem FolkmanDirectedFiniteStageAtlas.right_booleanLaws
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (A : FolkmanDirectedFiniteStageAtlas L R β)
    (x y : R) :
    (x + x = 0) ∧ (x * x = x) ∧ (x * y = y * x) := by
  classical
  let xs : Fin 0 → L := fun i => Fin.elim0 i
  let ys : Fin 2 → R := fun j => if j = 0 then x else y
  let w : FolkmanFiniteTupleStageWitness (β := β) xs ys :=
    Classical.choice (A.covers 0 2 xs ys)
  let a : AsBoolRing (Finset (Fin w.stage.atom.rightCount)) :=
    toBoolRing (w.rightTuple 0)
  let b : AsBoolRing (Finset (Fin w.stage.atom.rightCount)) :=
    toBoolRing (w.rightTuple 1)
  have ha : w.stage.right a = x := by
    simpa [ys, a] using w.right_spec 0
  have hb : w.stage.right b = y := by
    simpa [ys, b] using w.right_spec 1
  simpa only [ha, hb] using
    (booleanLaws_on_nonunitalRingHom_range w.stage.right a b)

end SuccessorTree.NonPrecompact
