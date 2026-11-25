import BANANA.NonPrecompact.BilinearResidue
import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.ModelTheory.Substructures

/-!
# Functional first-order presentation of the two BANANA sorts

On the disjoint union, constants name the two zeroes. A single binary addition
agrees with addition on each sort and returns its first argument on mixed
inputs. The tag and the pairing predicate are relational. Embeddings between
such structures are exactly pairs of pairing-preserving linear embeddings.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

inductive BananaFunctionalSymbol : ℕ → Type
  | leftZero : BananaFunctionalSymbol 0
  | rightZero : BananaFunctionalSymbol 0
  | add : BananaFunctionalSymbol 2

inductive BananaFunctionalRelation : ℕ → Type
  | left : BananaFunctionalRelation 1
  | edge : BananaFunctionalRelation 2

/-- Tags, totalised addition, the two zeroes and the pairing predicate. -/
def bananaFunctionalLanguage : Language where
  Functions := BananaFunctionalSymbol
  Relations := BananaFunctionalRelation

namespace BananaFunctional

variable {L R L' R' : Type*} [AddCommGroup L] [AddCommGroup R]
  [AddCommGroup L'] [AddCommGroup R']
  [Module F2 L] [Module F2 R] [Module F2 L'] [Module F2 R']

private def add : (L ⊕ R) → (L ⊕ R) → (L ⊕ R)
  | .inl x, .inl y => .inl (x + y)
  | .inr x, .inr y => .inr (x + y)
  | x, _ => x

private def isLeft : L ⊕ R → Prop
  | .inl _ => True
  | .inr _ => False

private def edge (β : L → R → F2) : (L ⊕ R) → (L ⊕ R) → Prop
  | .inl x, .inr y => β x y = 1
  | _, _ => False

/-- The structure associated with a specified pairing on the two sorts. -/
@[instance_reducible] def structureOn (β : L → R → F2) : bananaFunctionalLanguage.Structure (L ⊕ R) where
  funMap f x := match f with
    | .leftZero => .inl 0
    | .rightZero => .inr 0
    | .add => add (x 0) (x 1)
  RelMap r x := match r with
    | .left => isLeft (x 0)
    | .edge => edge β (x 0) (x 1)

/-- A pairing-preserving pair of injections gives a first-order embedding. -/
def embedding (β : L → R → F2) (γ : L' → R' → F2)
    (f : L →ₗ[F2] L') (g : R →ₗ[F2] R')
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hpair : ∀ x y, γ (f x) (g y) = β x y) :
    letI := structureOn β
    letI := structureOn γ
    (L ⊕ R) ↪[bananaFunctionalLanguage] (L' ⊕ R') := by
  letI := structureOn β
  letI := structureOn γ
  exact {
    toFun := Sum.map f g
    inj' := Sum.map_injective.mpr ⟨hf, hg⟩
    map_fun' := by
      intro n s x
      cases s with
      | leftZero => exact congrArg Sum.inl f.map_zero
      | rightZero => exact congrArg Sum.inr g.map_zero
      | add =>
        change Sum.map f g (add (x 0) (x 1)) = add (Sum.map f g (x 0)) (Sum.map f g (x 1))
        cases x 0 <;> cases x 1 <;> simp [add, map_add]
    map_rel' := by
      intro n r x
      cases r with
      | left =>
        change isLeft (Sum.map f g (x 0)) ↔ isLeft (x 0)
        cases x 0 <;> rfl
      | edge =>
        change edge γ (Sum.map f g (x 0)) (Sum.map f g (x 1)) ↔ edge β (x 0) (x 1)
        cases x 0 <;> cases x 1 <;> simp [edge, hpair] }

section Decode

variable (β : L → R → F2) (γ : L' → R' → F2)

variable (e : @Language.Embedding bananaFunctionalLanguage (L ⊕ R) (L' ⊕ R')
  (structureOn β) (structureOn γ))

private def imageLeft (x : L) : L' :=
  (e (.inl x)).elim id (fun _ => 0)

private def imageRight (x : R) : R' :=
  (e (.inr x)).elim (fun _ => 0) id

omit [Module F2 L] [Module F2 R] [Module F2 L'] [Module F2 R'] in
private theorem map_inl (x : L) : e (.inl x) = .inl (imageLeft β γ e x) := by
  let := structureOn β
  let := structureOn γ
  have h := (e.map_rel BananaFunctionalRelation.left (fun _ => Sum.inl x)).mpr trivial
  change isLeft (e (.inl x)) at h
  cases he : e (.inl x) <;> simp_all [imageLeft, isLeft]

omit [Module F2 L] [Module F2 R] [Module F2 L'] [Module F2 R'] in
private theorem map_inr (x : R) : e (.inr x) = .inr (imageRight β γ e x) := by
  let := structureOn β
  let := structureOn γ
  have h := (e.map_rel BananaFunctionalRelation.left (fun _ => Sum.inr x)).not.mpr
    (show ¬ isLeft (Sum.inr x : L ⊕ R) from id)
  change ¬ isLeft (e (.inr x)) at h
  cases he : e (.inr x) <;> simp_all [imageRight, isLeft]

private theorem imageLeft_add (x y : L) :
    imageLeft β γ e (x + y) = imageLeft β γ e x + imageLeft β γ e y := by
  let := structureOn β
  let := structureOn γ
  have h := e.map_fun BananaFunctionalSymbol.add ![Sum.inl x, Sum.inl y]
  change e (.inl (x + y)) = add (e (.inl x)) (e (.inl y)) at h
  rw [map_inl β γ e (x + y), map_inl β γ e x, map_inl β γ e y] at h
  exact Sum.inl.inj h

private theorem imageRight_add (x y : R) :
    imageRight β γ e (x + y) = imageRight β γ e x + imageRight β γ e y := by
  let := structureOn β
  let := structureOn γ
  have h := e.map_fun BananaFunctionalSymbol.add ![Sum.inr x, Sum.inr y]
  change e (.inr (x + y)) = add (e (.inr x)) (e (.inr y)) at h
  rw [map_inr β γ e (x + y), map_inr β γ e x, map_inr β γ e y] at h
  exact Sum.inr.inj h

/-- The left component of the first-order embedding. -/
def leftLinear : L →ₗ[F2] L' where
  toFun := imageLeft β γ e
  map_add' := imageLeft_add β γ e
  map_smul' c x := ZMod.map_smul (AddMonoidHom.mk' _ (imageLeft_add β γ e)) c x

/-- The right component of the first-order embedding. -/
def rightLinear : R →ₗ[F2] R' where
  toFun := imageRight β γ e
  map_add' := imageRight_add β γ e
  map_smul' c x := ZMod.map_smul (AddMonoidHom.mk' _ (imageRight_add β γ e)) c x

theorem map_inl_linear (x : L) : e (.inl x) = .inl (leftLinear β γ e x) :=
  map_inl β γ e x

theorem map_inr_linear (x : R) : e (.inr x) = .inr (rightLinear β γ e x) :=
  map_inr β γ e x

theorem leftLinear_injective : Function.Injective (leftLinear β γ e) := by
  intro x y h
  apply Sum.inl.inj (β := R)
  let := structureOn β
  let := structureOn γ
  apply e.injective
  rw [map_inl_linear β γ e x, map_inl_linear β γ e y, h]

theorem rightLinear_injective : Function.Injective (rightLinear β γ e) := by
  intro x y h
  apply Sum.inr.inj (α := L)
  let := structureOn β
  let := structureOn γ
  apply e.injective
  rw [map_inr_linear β γ e x, map_inr_linear β γ e y, h]

/-- In the two-element field the edge relation determines the pairing. -/
theorem map_pairing (x : L) (y : R) :
    γ (leftLinear β γ e x) (rightLinear β γ e y) = β x y := by
  let := structureOn β
  let := structureOn γ
  have h := e.map_rel BananaFunctionalRelation.edge ![Sum.inl x, Sum.inr y]
  change edge γ (e (.inl x)) (e (.inr y)) ↔ β x y = 1 at h
  rw [map_inl_linear β γ e x, map_inr_linear β γ e y] at h
  rcases f2_eq_zero_or_one (β x y) with h0 | h1
  · exact ((f2_eq_zero_or_one _).resolve_right (by simpa [h0, edge] using h)).trans h0.symm
  · exact (h.mpr h1).trans h1.symm

end Decode
section Substructures

variable (β : L → R → F2)

variable (S : @Language.Substructure bananaFunctionalLanguage (L ⊕ R) (structureOn β))

/-- Left sort of a closed first-order substructure. -/
def leftSubspace : Submodule F2 L where
  carrier := {x | Sum.inl x ∈ S}
  zero_mem' := by
    let := structureOn β
    exact S.fun_mem BananaFunctionalSymbol.leftZero Fin.elim0 (fun i => Fin.elim0 i)
  add_mem' {x y} hx hy := by
    let := structureOn β
    change Sum.inl (x + y) ∈ S
    exact S.fun_mem BananaFunctionalSymbol.add ![Sum.inl x, Sum.inl y]
      (fun i => Fin.cases hx (fun j => Fin.cases hy (fun k => Fin.elim0 k) j) i)
  smul_mem' c x hx := by
    let := structureOn β
    rcases f2_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul]
      exact S.fun_mem BananaFunctionalSymbol.leftZero Fin.elim0 (fun i => Fin.elim0 i)
    · simpa only [one_smul] using hx

/-- Right sort of a closed first-order substructure. -/
def rightSubspace : Submodule F2 R where
  carrier := {x | Sum.inr x ∈ S}
  zero_mem' := by
    let := structureOn β
    exact S.fun_mem BananaFunctionalSymbol.rightZero Fin.elim0 (fun i => Fin.elim0 i)
  add_mem' {x y} hx hy := by
    let := structureOn β
    change Sum.inr (x + y) ∈ S
    exact S.fun_mem BananaFunctionalSymbol.add ![Sum.inr x, Sum.inr y]
      (fun i => Fin.cases hx (fun j => Fin.cases hy (fun k => Fin.elim0 k) j) i)
  smul_mem' c x hx := by
    let := structureOn β
    rcases f2_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul]
      exact S.fun_mem BananaFunctionalSymbol.rightZero Fin.elim0 (fun i => Fin.elim0 i)
    · simpa only [one_smul] using hx

/-- The pairing induced on the two subspaces of a closed substructure. -/
def restrictedPairing (x : leftSubspace β S) (y : rightSubspace β S) : F2 :=
  β x y

/-- In a closed substructure the tags, operations and pairing are precisely
those of its two subspaces with the restricted pairing. -/
def substructureEquiv :
    letI := structureOn β
    letI := structureOn (restrictedPairing β S)
    ((leftSubspace β S) ⊕ (rightSubspace β S)) ≃[bananaFunctionalLanguage] S := by
  letI := structureOn β
  letI := structureOn (restrictedPairing β S)
  let incl : (leftSubspace β S ⊕ rightSubspace β S) → S := fun xy => match xy with
    | .inl x => ⟨.inl x, x.property⟩
    | .inr y => ⟨.inr y, y.property⟩
  exact {
    toEquiv := {
      toFun := incl
      invFun := fun z => match hz : z.val with
        | .inl x => .inl ⟨x, by
          change Sum.inl x ∈ S
          rw [← hz]
          exact z.property⟩
        | .inr y => .inr ⟨y, by
          change Sum.inr y ∈ S
          rw [← hz]
          exact z.property⟩
      left_inv := fun z => by cases z <;> rfl
      right_inv := fun ⟨z, _⟩ => by cases z <;> rfl }
    map_fun' := by
      intro n s x
      apply Subtype.ext
      cases s with
      | leftZero => rfl
      | rightZero => rfl
      | add =>
        change (incl (add (x 0) (x 1)) : L ⊕ R) =
          add (incl (x 0) : L ⊕ R) (incl (x 1) : L ⊕ R)
        cases x 0 <;> cases x 1 <;> rfl
    map_rel' := by
      intro n s x
      cases s with
      | left =>
        change isLeft (incl (x 0) : L ⊕ R) ↔ isLeft (x 0)
        cases x 0 <;> rfl
      | edge =>
        change edge β (incl (x 0) : L ⊕ R) (incl (x 1) : L ⊕ R) ↔
          edge (restrictedPairing β S) (x 0) (x 1)
        cases x 0 <;> cases x 1 <;> rfl }

theorem finite_leftSubspace [Finite S] : Finite (leftSubspace β S) :=
  Finite.of_injective
    (fun x : leftSubspace β S => (⟨Sum.inl (x : L), x.property⟩ : S))
    (fun _ _ h => Subtype.ext (Sum.inl.inj (congrArg Subtype.val h)))

theorem finite_rightSubspace [Finite S] : Finite (rightSubspace β S) :=
  Finite.of_injective
    (fun y : rightSubspace β S => (⟨Sum.inr (y : R), y.property⟩ : S))
    (fun _ _ h => Subtype.ext (Sum.inr.inj (congrArg Subtype.val h)))

end Substructures
end BananaFunctional
end SuccessorTree.NonPrecompact
