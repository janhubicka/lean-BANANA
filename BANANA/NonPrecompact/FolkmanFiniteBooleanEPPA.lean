import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Fintype.EquivFin

/-!
# The Folkman–BANANA two-atom EPPA obstruction

An automorphism preserves the order given by multiplication. In a finite
Boolean ring, it cannot map an element to a strict enlargement. The
explicit two-atom witness works in every finite non-unital extension.
-/

namespace SuccessorTree.NonPrecompact

/-- A Boolean-ring automorphism of a finite ring cannot map an element
strictly upwards in the order defined by multiplication. -/
theorem folkmanRingEquiv_cannot_enlarge
    {R : Type*} [BooleanRing R] [Finite R]
    (e : R ≃+* R) (a b : R) (hle : a * b = a) (hne : a ≠ b) :
    e a ≠ b := by
  classical
  intro h
  let Below (v : R) := {x : R // x * v = x}
  letI (v : R) : Fintype (Below v) := Fintype.ofFinite _
  let i : Below a → Below b := fun x =>
    ⟨x.val, by
      calc
        x.val * b = (x.val * a) * b := congrArg (fun y => y * b) x.property.symm
        _ = x.val := by rw [mul_assoc, hle, x.property]⟩
  let t : Below b := ⟨b, BooleanRing.mul_self _⟩
  have hti : t ∉ Set.range i := by
    rintro ⟨x, hx⟩
    have hx' : x.val = b := congrArg Subtype.val hx
    have hba : b * a = b := hx' ▸ x.property
    exact hne (hle.symm.trans ((mul_comm a b).trans hba))
  have hcard := Fintype.card_lt_of_injective_of_notMem i
    (fun x y hxy => Subtype.ext (congrArg (fun z : Below b => z.val) hxy)) hti
  let j : Below b → Below a := fun x =>
    ⟨e.symm x.val, by apply e.injective; simp [h, x.property]⟩
  have hj : Function.Injective j :=
    fun x y hxy => Subtype.ext (e.symm.injective
      (congrArg (fun z : Below a => z.val) hxy))
  exact (not_lt_of_ge (Fintype.card_le_of_injective j hj)) hcard

/-- In every finite Boolean-ring extension of the two-atom ring, an
automorphism fails to extend the left partial isomorphism sending the first
atom to the join of both atoms. The embedding can be non-unital. -/
theorem folkmanTwoAtom_partialIso_obstructed
    {R : Type*} [BooleanRing R] [Finite R]
    (f : AsBoolRing (Finset (Fin 2)) →ₙ+* R) (hf : Function.Injective f)
    (e : R ≃+* R) : e (f (toBoolRing {(0 : Fin 2)})) ≠ f 1 := by
  let a : AsBoolRing (Finset (Fin 2)) := toBoolRing {0}
  have ha1 : a ≠ 1 := by
    intro ha
    have h := congrArg ofBoolRing ha
    change ({0} : Finset (Fin 2)) = Finset.univ at h
    have hmem : (1 : Fin 2) ∈ ({0} : Finset (Fin 2)) := h.symm ▸ Finset.mem_univ _
    exact (by decide : (1 : Fin 2) ≠ 0) (Finset.mem_singleton.mp hmem)
  exact folkmanRingEquiv_cannot_enlarge e (f a) (f 1)
    ((map_mul f a 1).symm.trans (congrArg f (mul_one a)))
    (fun h => ha1 (hf h))

end SuccessorTree.NonPrecompact
