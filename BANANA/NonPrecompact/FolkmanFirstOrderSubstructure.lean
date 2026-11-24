import BANANA.NonPrecompact.FolkmanFirstOrder
import BANANA.NonPrecompact.FolkmanNativeFiniteHeredity

/-!
# Substructures in the first-order Folkman encoding

A substructure of the product is the product of its two coordinate subrings.
The projections extract the two coordinates, and the addition of elements
on the two axes reconstructs their pair. Finite substructures therefore
recover the native finite class by giving each subring its own identity.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

section

variable {L R : Type*} [BooleanRing L] [BooleanRing R]
variable (p : L → R → F2)
variable (S : @Language.Substructure folkmanLanguage (L × R) (folkmanProductStructure p))

/-- The left coordinate subring of a first-order substructure. -/
def folkmanProductSubstructureLeft : NonUnitalSubring L := by
  letI := folkmanProductStructure p
  exact folkmanNativeSubringOfClosed {x | (x, 0) ∈ S}
    (S.fun_mem (FolkmanFunction.zero : folkmanLanguage.Functions 0)
      Fin.elim0 (fun i => (i.elim0 : False).elim))
    (fun x y hx hy => by
      have h := S.fun_mem (FolkmanFunction.add : folkmanLanguage.Functions 2)
        ![(x, 0), (y, 0)] (by
          intro i
          fin_cases i
          · exact hx
          · exact hy)
      change (x + y, (0 : R) + 0) ∈ S at h
      change (x + y, (0 : R)) ∈ S
      simpa only [zero_add] using h)
    (fun x y hx hy => by
      have h := S.fun_mem (FolkmanFunction.mul : folkmanLanguage.Functions 2)
        ![(x, 0), (y, 0)] (by
          intro i
          fin_cases i
          · exact hx
          · exact hy)
      change (x * y, (0 : R) * 0) ∈ S at h
      change (x * y, (0 : R)) ∈ S
      simpa only [mul_zero] using h)

/-- The right coordinate subring of a first-order substructure. -/
def folkmanProductSubstructureRight : NonUnitalSubring R := by
  letI := folkmanProductStructure p
  exact folkmanNativeSubringOfClosed {y | (0, y) ∈ S}
    (S.fun_mem (FolkmanFunction.zero : folkmanLanguage.Functions 0)
      Fin.elim0 (fun i => (i.elim0 : False).elim))
    (fun x y hx hy => by
      have h := S.fun_mem (FolkmanFunction.add : folkmanLanguage.Functions 2)
        ![(0, x), (0, y)] (by
          intro i
          fin_cases i
          · exact hx
          · exact hy)
      change ((0 : L) + 0, x + y) ∈ S at h
      change ((0 : L), x + y) ∈ S
      simpa only [zero_add] using h)
    (fun x y hx hy => by
      have h := S.fun_mem (FolkmanFunction.mul : folkmanLanguage.Functions 2)
        ![(0, x), (0, y)] (by
          intro i
          fin_cases i
          · exact hx
          · exact hy)
      change ((0 : L) * 0, x * y) ∈ S at h
      change ((0 : L), x * y) ∈ S
      simpa only [mul_zero] using h)

theorem folkmanProductSubstructure_mem_iff (xy : L × R) :
    xy ∈ S ↔ xy.1 ∈ folkmanProductSubstructureLeft p S ∧
      xy.2 ∈ folkmanProductSubstructureRight p S := by
  let _ := folkmanProductStructure p
  constructor
  · intro h
    exact ⟨S.fun_mem (FolkmanFunction.left : folkmanLanguage.Functions 1)
      (fun _ => xy) (fun _ => h),
      S.fun_mem (FolkmanFunction.right : folkmanLanguage.Functions 1)
        (fun _ => xy) (fun _ => h)⟩
  · rintro ⟨hx, hy⟩
    have h := S.fun_mem (FolkmanFunction.add : folkmanLanguage.Functions 2)
      ![(xy.1, 0), (0, xy.2)] (by
        intro i
        fin_cases i
        · exact hx
        · exact hy)
    change (xy.1 + 0, 0 + xy.2) ∈ S at h
    simpa only [add_zero, zero_add, Prod.eta] using h

/-- A substructure and the product of the two coordinate subrings are
isomorphic in the first-order language, with its original pairing. -/
def folkmanProductSubstructureEquiv :
    letI := folkmanProductStructure p
    letI := folkmanProductStructure
      (fun x : folkmanProductSubstructureLeft p S =>
        fun y : folkmanProductSubstructureRight p S => p x y)
    (folkmanProductSubstructureLeft p S × folkmanProductSubstructureRight p S)
      ≃[folkmanLanguage] S := by
  letI := folkmanProductStructure p
  letI := folkmanProductStructure
    (fun x : folkmanProductSubstructureLeft p S =>
      fun y : folkmanProductSubstructureRight p S => p x y)
  exact {
    toFun := fun xy => ⟨(xy.1, xy.2), (folkmanProductSubstructure_mem_iff p S _).mpr
      ⟨xy.1.property, xy.2.property⟩⟩
    invFun := fun a =>
      let h := (folkmanProductSubstructure_mem_iff p S a).mp a.property
      (⟨a.val.1, h.1⟩, ⟨a.val.2, h.2⟩)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_fun' := by
      intro n op xs
      cases op <;> rfl
    map_rel' := by
      intro n r xs
      cases r
      exact Iff.rfl }

end

end SuccessorTree.NonPrecompact
