import BANANA.NonPrecompact.FolkmanAtomCode

/-!
# Homomorphisms from a one-atom Boolean ring

The single nonzero generator determines a non-unital map. It gives an
embedding exactly when its image is nonzero.
-/

namespace SuccessorTree.NonPrecompact

abbrev FolkmanOneAtomRing := FolkmanNativeCodeRing 1

theorem folkmanOneAtom_eq_zero_or_one (x : FolkmanOneAtomRing) : x = 0 ∨ x = 1 := by
  by_cases h : (0 : Fin 1) ∈ ofBoolRing x
  · right
    apply ofBoolRing.injective
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change (0 : Fin 1) ∈ ofBoolRing x ↔ (0 : Fin 1) ∈ (Finset.univ : Finset (Fin 1))
    simp [h]
  · left
    apply ofBoolRing.injective
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change (0 : Fin 1) ∈ ofBoolRing x ↔ (0 : Fin 1) ∈ (∅ : Finset (Fin 1))
    simp [h]

theorem folkmanOneAtom_one_ne_zero : (1 : FolkmanOneAtomRing) ≠ 0 := by
  intro h
  have eq := congrArg ofBoolRing h
  change (Finset.univ : Finset (Fin 1)) = ∅ at eq
  exact (Finset.notMem_empty _) (eq ▸ Finset.mem_univ (0 : Fin 1))

/-- The non-unital homomorphism from a one-atom Boolean ring sending its atom to `x`. -/
noncomputable def folkmanOneAtomHom {R : Type*} [BooleanRing R] (x : R) :
    FolkmanOneAtomRing →ₙ+* R := by
  classical
  exact
    { toFun := fun t => if t = 0 then 0 else x
      map_zero' := ite_eq_left rfl
      map_add' := fun a b => by
        rcases folkmanOneAtom_eq_zero_or_one a with rfl | rfl <;>
          rcases folkmanOneAtom_eq_zero_or_one b with rfl | rfl <;>
          simp [folkmanOneAtom_one_ne_zero, BooleanRing.add_self]
      map_mul' := fun a b => by
        rcases folkmanOneAtom_eq_zero_or_one a with rfl | rfl <;>
          rcases folkmanOneAtom_eq_zero_or_one b with rfl | rfl <;>
          simp [folkmanOneAtom_one_ne_zero, BooleanRing.mul_self] }

@[simp] theorem folkmanOneAtomHom_one {R : Type*} [BooleanRing R] (x : R) :
    folkmanOneAtomHom x 1 = x := by
  classical
  change (if (1 : FolkmanOneAtomRing) = 0 then 0 else x) = x
  exact ite_eq_right folkmanOneAtom_one_ne_zero

theorem folkmanOneAtomHom_injective {R : Type*} [BooleanRing R] {x : R} (hx : x ≠ 0) :
    Function.Injective (folkmanOneAtomHom x) := by
  intro a b hab
  rcases folkmanOneAtom_eq_zero_or_one a with rfl | rfl <;>
    rcases folkmanOneAtom_eq_zero_or_one b with rfl | rfl
  · rfl
  · exact (hx (by simpa using hab.symm)).elim
  · exact (hx (by simpa using hab)).elim
  · rfl

theorem folkmanOneAtomHom_range {R : Type*} [BooleanRing R]
    (f : FolkmanOneAtomRing →ₙ+* R) : Set.range f = {0, f 1} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rcases folkmanOneAtom_eq_zero_or_one a with rfl | rfl <;> simp
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · exact Set.mem_range_self _

end SuccessorTree.NonPrecompact
