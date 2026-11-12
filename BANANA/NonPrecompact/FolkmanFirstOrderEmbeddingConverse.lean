import BANANA.NonPrecompact.FolkmanFirstOrderNativeEmbedding
import Mathlib.Tactic.FinCases

/-!
# Recovering native Folkman pair embeddings from tagged first-order embeddings

The tagged finite language has separate left/right zero constants,
binary operations for each non-unital ring, two sort predicates and
a binary relation expressing that the original F₂ pairing is one.

An embedding of the tagged first-order structures cannot exchange
the sorts. Restriction to each sort preserves its ring operations
and zero. Reflection of the pairing-one relation is equivalent to
preserving every F₂-valued pairing, since F₂ has two elements.

This is the reverse direction of the native/first-order embedding
adapter; its proof does not use ambient units, finiteness, or a
Fraisse-limit theorem.

Source draft: pinned local Lean kernel verification remains required.
-/

namespace SuccessorTree.NonPrecompact

open scoped FirstOrder

/-- Original non-unital two-sort pairing embeddings. This type
also applies to the potentially non-unital ambient countable
Folkman model, unlike the finite BooleanRing-only interfaces. -/
structure FolkmanOriginalPairingEmbedding
    {AL AR BL BR : Type*}
    [NonUnitalRing AL] [NonUnitalRing AR]
    [NonUnitalRing BL] [NonUnitalRing BR]
    (βA : AL → AR → F2) (βB : BL → BR → F2) where
  left : AL →ₙ+* BL
  right : AR →ₙ+* BR
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  preserves_pairing : ∀ x y, βB (left x) (right y) = βA x y

/-- Native pairing embeddings induce first-order embeddings of
the fully tagged structures. -/
noncomputable def FolkmanOriginalPairingEmbedding.toFirstOrder
    {AL AR BL BR : Type*}
    [NonUnitalRing AL] [NonUnitalRing AR]
    [NonUnitalRing BL] [NonUnitalRing BR]
    {βA : AL → AR → F2} {βB : BL → BR → F2}
    (e : FolkmanOriginalPairingEmbedding βA βB) :
    @FirstOrder.Language.Embedding folkmanFirstOrderLanguage
      (Sum AL AR) (Sum BL BR)
      (folkmanTaggedFirstOrderStructure AL AR βA)
      (folkmanTaggedFirstOrderStructure BL BR βB) :=
  folkmanTaggedFirstOrderEmbeddingOfNative
    e.left e.right e.left_injective e.right_injective e.preserves_pairing

/-- The pairing-one predicate distinguishes the two F₂ values.
This small finite fact is needed to recover the ORIGINAL full
pairing from reflection of the one-valued relation. -/
theorem folkmanF2_eq_of_one_iff_one
    (a b : F2) (h : (a = 1 ↔ b = 1)) : a = b := by
  have hcases (x : F2) : x = 0 ∨ x = 1 := by
    fin_cases x <;> decide
  rcases hcases a with ha | ha
  · rcases hcases b with hb | hb
    · exact ha.trans hb.symm
    · have hab : (0 : F2) = 1 := ha.symm.trans (h.mpr hb)
      have h01 : (0 : F2) ≠ 1 := by decide
      exact False.elim (h01 hab)
  · exact ha.trans (h.mp ha).symm

/-- Recover a faithful pair of original non-unital ring embeddings
from any embedding of the tagged first-order structures.

Preservation of the two unary sort predicates forces the tagged
map to restrict to one map on each ring sort. The zero constants
and four ring operations force those restrictions to be
non-unital ring homomorphisms. Pairing relation reflection
then gives equality of every original F₂-valued pairing. -/
noncomputable def folkmanOriginalPairingEmbeddingOfFirstOrder
    {AL AR BL BR : Type*}
    [NonUnitalRing AL] [NonUnitalRing AR]
    [NonUnitalRing BL] [NonUnitalRing BR]
    {βA : AL → AR → F2}
    {βB : BL → BR → F2}
    (e : @FirstOrder.Language.Embedding folkmanFirstOrderLanguage
      (Sum AL AR) (Sum BL BR)
      (folkmanTaggedFirstOrderStructure AL AR βA)
      (folkmanTaggedFirstOrderStructure BL BR βB)) :
    FolkmanOriginalPairingEmbedding βA βB := by
  classical
  letI : folkmanFirstOrderLanguage.Structure (Sum AL AR) :=
    folkmanTaggedFirstOrderStructure AL AR βA
  letI : folkmanFirstOrderLanguage.Structure (Sum BL BR) :=
    folkmanTaggedFirstOrderStructure BL BR βB
  have leftTag (x : AL) : folkmanTaggedIsLeft (e (.inl x)) := by
    have h := (e.map_rel
      (0 : folkmanFirstOrderLanguage.Relations 1)
      (fun _ : Fin 1 => (Sum.inl x : Sum AL AR))).mpr
    have hsource :
        FirstOrder.Language.Structure.RelMap
          (0 : folkmanFirstOrderLanguage.Relations 1)
          (fun _ : Fin 1 => (Sum.inl x : Sum AL AR)) := by
      change folkmanTaggedIsLeft (Sum.inl x)
      trivial
    have htarget := h hsource
    change folkmanTaggedIsLeft (e (.inl x)) at htarget
    exact htarget
  have rightTag (y : AR) : folkmanTaggedIsRight (e (.inr y)) := by
    have h := (e.map_rel
      (1 : folkmanFirstOrderLanguage.Relations 1)
      (fun _ : Fin 1 => (Sum.inr y : Sum AL AR))).mpr
    have hsource :
        FirstOrder.Language.Structure.RelMap
          (1 : folkmanFirstOrderLanguage.Relations 1)
          (fun _ : Fin 1 => (Sum.inr y : Sum AL AR)) := by
      change folkmanTaggedIsRight (Sum.inr y)
      trivial
    have htarget := h hsource
    change folkmanTaggedIsRight (e (.inr y)) at htarget
    exact htarget
  have leftImage (x : AL) : ∃ y : BL, e (.inl x) = .inl y := by
    cases he : e (.inl x) with
    | inl y => exact ⟨y, he⟩
    | inr y =>
        have h := leftTag x
        simp [folkmanTaggedIsLeft, he] at h
  have rightImage (y : AR) : ∃ z : BR, e (.inr y) = .inr z := by
    cases he : e (.inr y) with
    | inl x =>
        have h := rightTag y
        simp [folkmanTaggedIsRight, he] at h
    | inr z => exact ⟨z, he⟩
  let fL : AL → BL := fun x => Classical.choose (leftImage x)
  let fR : AR → BR := fun y => Classical.choose (rightImage y)
  have hL (x : AL) : e (.inl x) = .inl (fL x) :=
    Classical.choose_spec (leftImage x)
  have hR (y : AR) : e (.inr y) = .inr (fR y) :=
    Classical.choose_spec (rightImage y)
  have hzL : fL 0 = 0 := by
    have h := e.map_constants
      (0 : folkmanFirstOrderLanguage.Constants)
    change e (Sum.inl (0 : AL)) = Sum.inl (0 : BL) at h
    exact Sum.inl.inj ((hL 0).symm.trans h)
  have hzR : fR 0 = 0 := by
    have h := e.map_constants
      (1 : folkmanFirstOrderLanguage.Constants)
    change e (Sum.inr (0 : AR)) = Sum.inr (0 : BR) at h
    exact Sum.inr.inj ((hR 0).symm.trans h)
  have haddL (x y : AL) : fL (x + y) = fL x + fL y := by
    let a : Fin 2 → Sum AL AR :=
      fun i => if i = 0 then .inl x else .inl y
    have h := e.map_fun (0 : folkmanFirstOrderLanguage.Functions 2) a
    change e (.inl (x + y)) =
      folkmanTaggedAddLeft (e (.inl x)) (e (.inl y)) at h
    have h' : (Sum.inl (fL (x + y)) : Sum BL BR) =
        .inl (fL x + fL y) := by
      calc
        Sum.inl (fL (x + y)) = e (.inl (x + y)) :=
          (hL (x + y)).symm
        _ = folkmanTaggedAddLeft (e (.inl x)) (e (.inl y)) := h
        _ = .inl (fL x + fL y) := by rw [hL x, hL y]; rfl
    exact Sum.inl.inj h'
  have hmulL (x y : AL) : fL (x * y) = fL x * fL y := by
    let a : Fin 2 → Sum AL AR :=
      fun i => if i = 0 then .inl x else .inl y
    have h := e.map_fun (1 : folkmanFirstOrderLanguage.Functions 2) a
    change e (.inl (x * y)) =
      folkmanTaggedMulLeft (e (.inl x)) (e (.inl y)) at h
    have h' : (Sum.inl (fL (x * y)) : Sum BL BR) =
        .inl (fL x * fL y) := by
      calc
        Sum.inl (fL (x * y)) = e (.inl (x * y)) :=
          (hL (x * y)).symm
        _ = folkmanTaggedMulLeft (e (.inl x)) (e (.inl y)) := h
        _ = .inl (fL x * fL y) := by rw [hL x, hL y]; rfl
    exact Sum.inl.inj h'
  have haddR (x y : AR) : fR (x + y) = fR x + fR y := by
    let a : Fin 2 → Sum AL AR :=
      fun i => if i = 0 then .inr x else .inr y
    have h := e.map_fun (2 : folkmanFirstOrderLanguage.Functions 2) a
    change e (.inr (x + y)) =
      folkmanTaggedAddRight (e (.inr x)) (e (.inr y)) at h
    have h' : (Sum.inr (fR (x + y)) : Sum BL BR) =
        .inr (fR x + fR y) := by
      calc
        Sum.inr (fR (x + y)) = e (.inr (x + y)) :=
          (hR (x + y)).symm
        _ = folkmanTaggedAddRight (e (.inr x)) (e (.inr y)) := h
        _ = .inr (fR x + fR y) := by rw [hR x, hR y]; rfl
    exact Sum.inr.inj h'
  have hmulR (x y : AR) : fR (x * y) = fR x * fR y := by
    let a : Fin 2 → Sum AL AR :=
      fun i => if i = 0 then .inr x else .inr y
    have h := e.map_fun (3 : folkmanFirstOrderLanguage.Functions 2) a
    change e (.inr (x * y)) =
      folkmanTaggedMulRight (e (.inr x)) (e (.inr y)) at h
    have h' : (Sum.inr (fR (x * y)) : Sum BL BR) =
        .inr (fR x * fR y) := by
      calc
        Sum.inr (fR (x * y)) = e (.inr (x * y)) :=
          (hR (x * y)).symm
        _ = folkmanTaggedMulRight (e (.inr x)) (e (.inr y)) := h
        _ = .inr (fR x * fR y) := by rw [hR x, hR y]; rfl
    exact Sum.inr.inj h'
  let gL : AL →ₙ+* BL :=
    { toFun := fL
      map_zero' := hzL
      map_add' := haddL
      map_mul' := hmulL }
  let gR : AR →ₙ+* BR :=
    { toFun := fR
      map_zero' := hzR
      map_add' := haddR
      map_mul' := hmulR }
  have hInjL : Function.Injective gL := by
    intro x y hxy
    apply Sum.inl.inj
    apply e.injective
    calc
      e (.inl x) = .inl (fL x) := hL x
      _ = .inl (fL y) := congrArg Sum.inl hxy
      _ = e (.inl y) := (hL y).symm
  have hInjR : Function.Injective gR := by
    intro x y hxy
    apply Sum.inr.inj
    apply e.injective
    calc
      e (.inr x) = .inr (fR x) := hR x
      _ = .inr (fR y) := congrArg Sum.inr hxy
      _ = e (.inr y) := (hR y).symm
  refine {
    left := gL
    right := gR
    left_injective := hInjL
    right_injective := hInjR
    preserves_pairing := ?_
  }
  intro x y
  let a : Fin 2 → Sum AL AR :=
    fun i => if i = 0 then .inl x else .inr y
  have h := e.map_rel
    (PUnit.unit : folkmanFirstOrderLanguage.Relations 2) a
  change folkmanTaggedPairingOne βB (e (.inl x)) (e (.inr y)) ↔
    folkmanTaggedPairingOne βA (.inl x) (.inr y) at h
  rw [hL x, hR y] at h
  change (βB (fL x) (fR y) = 1) ↔ (βA x y = 1) at h
  exact folkmanF2_eq_of_one_iff_one _ _ h

end SuccessorTree.NonPrecompact
