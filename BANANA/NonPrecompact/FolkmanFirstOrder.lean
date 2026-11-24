import BANANA.NonPrecompact.FolkmanNativePairingEmbedding
import Mathlib.ModelTheory.Substructures

/-!
# A first-order encoding of paired rings

Mathlib uses one-sorted languages. The product of the two rings records both
sorts, with coordinate projections `(x, y) ↦ (x, 0)` and `(x, y) ↦ (0, y)`
that force each embedding to act on the two coordinates separately. The ring
operations are componentwise, and pairing relations read a left coordinate
and a right coordinate. There is no symbol for a multiplicative unit.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

/-- Product ring operations and the two sort projections. -/
inductive FolkmanFunction : ℕ → Type
  | zero : FolkmanFunction 0
  | add : FolkmanFunction 2
  | mul : FolkmanFunction 2
  | left : FolkmanFunction 1
  | right : FolkmanFunction 1

/-- One binary relation for each value of the pairing. -/
inductive FolkmanRelation : ℕ → Type
  | pair (a : ZMod 2) : FolkmanRelation 2

def folkmanLanguage : Language where
  Functions := FolkmanFunction
  Relations := FolkmanRelation

instance : Countable (Σ n, folkmanLanguage.Functions n) :=
  (show Function.Injective (fun x : (Σ n, folkmanLanguage.Functions n) => match x with
    | ⟨_, FolkmanFunction.zero⟩ => (0 : ℕ)
    | ⟨_, FolkmanFunction.add⟩ => 1
    | ⟨_, FolkmanFunction.mul⟩ => 2
    | ⟨_, FolkmanFunction.left⟩ => 3
    | ⟨_, FolkmanFunction.right⟩ => 4) from (by
      rintro ⟨_, f⟩ ⟨_, g⟩
      cases f <;> cases g <;> simp)).countable

@[instance_reducible]
def folkmanProductStructure {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    (p : L → R → ZMod 2) : folkmanLanguage.Structure (L × R) where
  funMap {_} f xs := match f with
    | .zero => 0
    | .add => xs 0 + xs 1
    | .mul => xs 0 * xs 1
    | .left => ((xs 0).1, 0)
    | .right => (0, (xs 0).2)
  RelMap {_} r xs := match r with
    | .pair a => p (xs 0).1 (xs 1).2 = a

section Embedding

variable {L R L' R' : Type*}
variable [NonUnitalRing L] [NonUnitalRing R] [NonUnitalRing L'] [NonUnitalRing R']
variable (p : L → R → ZMod 2) (q : L' → R' → ZMod 2)

/-- A pair of injective non-unital ring maps preserving the cross-pairing
gives a first-order embedding of the product structures. -/
def folkmanProductEmbedding (f : L →ₙ+* L') (g : R →ₙ+* R')
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : ∀ x y, q (f x) (g y) = p x y) :
    letI := folkmanProductStructure p
    letI := folkmanProductStructure q
    (L × R) ↪[folkmanLanguage] (L' × R') := by
  letI := folkmanProductStructure p
  letI := folkmanProductStructure q
  exact {
    toFun := fun xy => (f xy.1, g xy.2)
    inj' := fun x y e => Prod.ext (hf (congrArg Prod.fst e)) (hg (congrArg Prod.snd e))
    map_fun' := by
      intro n op xs
      cases op with
      | zero => exact Prod.ext (map_zero f) (map_zero g)
      | add => exact Prod.ext (map_add f _ _) (map_add g _ _)
      | mul => exact Prod.ext (map_mul f _ _) (map_mul g _ _)
      | left => exact Prod.ext rfl (map_zero g)
      | right => exact Prod.ext (map_zero f) rfl
    map_rel' := by
      intro n r xs
      cases r with
      | pair a =>
        change q (f (xs 0).1) (g (xs 1).2) = a ↔ p (xs 0).1 (xs 1).2 = a
        rw [h] }

variable (e : letI := folkmanProductStructure p; letI := folkmanProductStructure q
  (L × R) ↪[folkmanLanguage] (L' × R'))

/-- The left coordinate map of a product-language embedding. -/
def folkmanProductEmbeddingLeft : L →ₙ+* L' := by
  letI := folkmanProductStructure p
  letI := folkmanProductStructure q
  exact {
    toFun := fun x => (e (x, 0)).1
    map_zero' := congrArg Prod.fst (e.map_fun
      (FolkmanFunction.zero : folkmanLanguage.Functions 0) Fin.elim0)
    map_add' := by
      intro x y
      have h := congrArg Prod.fst
        (e.map_fun (FolkmanFunction.add : folkmanLanguage.Functions 2) ![(x, 0), (y, 0)])
      change (e (x + y, (0 : R) + 0)).1 = (e (x, 0)).1 + (e (y, 0)).1 at h
      simpa only [zero_add] using h
    map_mul' := by
      intro x y
      have h := congrArg Prod.fst
        (e.map_fun (FolkmanFunction.mul : folkmanLanguage.Functions 2) ![(x, 0), (y, 0)])
      change (e (x * y, (0 : R) * 0)).1 = (e (x, 0)).1 * (e (y, 0)).1 at h
      simpa only [mul_zero] using h }

/-- The right coordinate map of a product-language embedding. -/
def folkmanProductEmbeddingRight : R →ₙ+* R' := by
  letI := folkmanProductStructure p
  letI := folkmanProductStructure q
  exact {
    toFun := fun y => (e (0, y)).2
    map_zero' := congrArg Prod.snd (e.map_fun
      (FolkmanFunction.zero : folkmanLanguage.Functions 0) Fin.elim0)
    map_add' := by
      intro x y
      have h := congrArg Prod.snd
        (e.map_fun (FolkmanFunction.add : folkmanLanguage.Functions 2) ![(0, x), (0, y)])
      change (e ((0 : L) + 0, x + y)).2 = (e (0, x)).2 + (e (0, y)).2 at h
      simpa only [zero_add] using h
    map_mul' := by
      intro x y
      have h := congrArg Prod.snd
        (e.map_fun (FolkmanFunction.mul : folkmanLanguage.Functions 2) ![(0, x), (0, y)])
      change (e ((0 : L) * 0, x * y)).2 = (e (0, x)).2 * (e (0, y)).2 at h
      simpa only [mul_zero] using h }

theorem folkmanProductEmbedding_split : ∀ a : L × R,
    e a = (folkmanProductEmbeddingLeft p q e a.1, folkmanProductEmbeddingRight p q e a.2) := by
  let _ := folkmanProductStructure p
  let _ := folkmanProductStructure q
  intro a
  apply Prod.ext
  · exact (congrArg Prod.fst (e.map_fun
     (FolkmanFunction.left : folkmanLanguage.Functions 1) (fun _ => a))).symm
  · exact (congrArg Prod.snd (e.map_fun
     (FolkmanFunction.right : folkmanLanguage.Functions 1) (fun _ => a))).symm

theorem folkmanProductEmbeddingLeft_injective :
    Function.Injective (folkmanProductEmbeddingLeft p q e) := by
  let _ := folkmanProductStructure p
  let _ := folkmanProductStructure q
  intro x y h
  have h' : e (x, 0) = e (y, 0) := by
    rw [folkmanProductEmbedding_split p q e (x, 0), folkmanProductEmbedding_split p q e (y, 0)]
    exact Prod.ext h rfl
  exact congrArg Prod.fst (e.injective h')

theorem folkmanProductEmbeddingRight_injective :
    Function.Injective (folkmanProductEmbeddingRight p q e) := by
  let _ := folkmanProductStructure p
  let _ := folkmanProductStructure q
  intro x y h
  have h' : e (0, x) = e (0, y) := by
    rw [folkmanProductEmbedding_split p q e (0, x), folkmanProductEmbedding_split p q e (0, y)]
    exact Prod.ext rfl h
  exact congrArg Prod.snd (e.injective h')

theorem folkmanProductEmbedding_preserves_pairing (x : L) (y : R) :
    q (folkmanProductEmbeddingLeft p q e x) (folkmanProductEmbeddingRight p q e y) = p x y := by
  let _ := folkmanProductStructure p
  let _ := folkmanProductStructure q
  exact (e.map_rel (FolkmanRelation.pair (p x y) : folkmanLanguage.Relations 2)
    ![(x, 0), (0, y)]).mpr rfl

end Embedding

/-- The first-order encoding has exactly the original native embeddings. -/
noncomputable def folkmanNativePairingEmbeddingEquiv
    {L R L' R' : Type*} [BooleanRing L] [BooleanRing R] [BooleanRing L'] [BooleanRing R']
    (P : FolkmanNativeFinitePairing L R) (Q : FolkmanNativeFinitePairing L' R') :
    letI := folkmanProductStructure P.pairing
    letI := folkmanProductStructure Q.pairing
    FolkmanNativePairingEmbedding P Q ≃ ((L × R) ↪[folkmanLanguage] (L' × R')) := by
  letI := folkmanProductStructure P.pairing
  letI := folkmanProductStructure Q.pairing
  exact {
    toFun := fun f => folkmanProductEmbedding P.pairing Q.pairing f.left f.right
      f.left_injective f.right_injective f.preserves_pairing
    invFun := fun e => {
      left := folkmanProductEmbeddingLeft _ _ e
      right := folkmanProductEmbeddingRight _ _ e
      left_injective := folkmanProductEmbeddingLeft_injective _ _ e
      right_injective := folkmanProductEmbeddingRight_injective _ _ e
      preserves_pairing := folkmanProductEmbedding_preserves_pairing _ _ e }
    left_inv := by
      intro f
      cases f
      rfl
    right_inv := by
      intro e
      apply Language.Embedding.ext
      intro xy
      exact (folkmanProductEmbedding_split _ _ e xy).symm }

end SuccessorTree.NonPrecompact
