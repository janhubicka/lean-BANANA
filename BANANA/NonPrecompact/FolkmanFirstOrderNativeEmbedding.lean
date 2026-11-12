import BANANA.NonPrecompact.FolkmanFirstOrderInterpretation

/-!
# Native non-unital Folkman embeddings as first-order embeddings

Any injective non-unital ring map on both original sorts preserving
all values of the F₂ cross-pairing gives an embedding of the tagged
first-order encodings. The two ring zeros remain separate constants,
and the source/target sort tags and pairing relation are reflected.

This establishes the native-to-first-order direction of the adapter
needed to apply the classical Fraisse-existence theorem to the
merged finite native Folkman class. The reverse direction, faithful
identification of generated substructures, and the countable limit
construction are separate implementation obligations.

Source-only until exact-head Lean elaboration and axiom inspection.
-/

namespace SuccessorTree.NonPrecompact

open scoped FirstOrder

/-- The map between tagged carriers induced by native two-sort maps. -/
def folkmanTaggedNativeMap
    {AL AR BL BR : Type*}
    (fL : AL → BL) (fR : AR → BR) :
    Sum AL AR → Sum BL BR
  | .inl x => .inl (fL x)
  | .inr y => .inr (fR y)

/-- Injectivity on both native sorts implies injectivity on their
disjoint sum (without any cardinality assumptions). -/
theorem folkmanTaggedNativeMap_injective
    {AL AR BL BR : Type*}
    (fL : AL → BL) (fR : AR → BR)
    (hL : Function.Injective fL)
    (hR : Function.Injective fR) :
    Function.Injective (folkmanTaggedNativeMap fL fR) := by
  intro x y hxy
  cases x with
  | inl a =>
      cases y with
      | inl b =>
          exact congrArg Sum.inl (hL (Sum.inl.inj hxy))
      | inr b =>
          cases hxy
  | inr a =>
      cases y with
      | inl b =>
          cases hxy
      | inr b =>
          exact congrArg Sum.inr (hR (Sum.inr.inj hxy))

/-- Every native pair of injective non-unital ring homomorphisms
preserving the COMPLETE original pairing gives an embedding of
the full tagged first-order structures. Relation reflection is
essential and uses the actual F₂ pairing equation. -/
noncomputable def folkmanTaggedFirstOrderEmbeddingOfNative
    {AL AR BL BR : Type*}
    [NonUnitalRing AL] [NonUnitalRing AR]
    [NonUnitalRing BL] [NonUnitalRing BR]
    {βA : AL → AR → F2}
    {βB : BL → BR → F2}
    (fL : AL →ₙ+* BL) (fR : AR →ₙ+* BR)
    (hL : Function.Injective fL)
    (hR : Function.Injective fR)
    (hPair : ∀ x y, βB (fL x) (fR y) = βA x y) :
    @FirstOrder.Language.Embedding folkmanFirstOrderLanguage
      (Sum AL AR) (Sum BL BR)
      (folkmanTaggedFirstOrderStructure AL AR βA)
      (folkmanTaggedFirstOrderStructure BL BR βB) := by
  classical
  letI : folkmanFirstOrderLanguage.Structure (Sum AL AR) :=
    folkmanTaggedFirstOrderStructure AL AR βA
  letI : folkmanFirstOrderLanguage.Structure (Sum BL BR) :=
    folkmanTaggedFirstOrderStructure BL BR βB
  refine {
    toFun := folkmanTaggedNativeMap fL fR
    inj' := folkmanTaggedNativeMap_injective fL fR hL hR
    map_fun' := ?_
    map_rel' := ?_
  }
  · intro n sym args
    by_cases hn0 : n = 0
    · subst n
      change Fin 2 at sym
      fin_cases sym <;>
        simp [folkmanTaggedFirstOrderStructure,
          folkmanTaggedNativeMap, map_zero]
    · by_cases hn2 : n = 2
      · subst n
        change Fin 4 at sym
        fin_cases sym <;>
          cases hx : args 0 <;>
          cases hy : args 1 <;>
          simp [folkmanTaggedFirstOrderStructure,
            folkmanTaggedNativeMap, folkmanTaggedAddLeft,
            folkmanTaggedMulLeft, folkmanTaggedAddRight,
            folkmanTaggedMulRight, hx, hy,
            map_zero, map_add, map_mul]
      · have he : IsEmpty (folkmanFirstOrderLanguage.Functions n) := by
          change IsEmpty (folkmanFirstOrderFunctions n)
          simp [folkmanFirstOrderFunctions, hn0, hn2]
        exact isEmptyElim sym
  · intro n rel args
    by_cases hn1 : n = 1
    · subst n
      change Fin 2 at rel
      fin_cases rel <;>
        cases hx : args 0 <;>
        simp [folkmanTaggedFirstOrderStructure,
          folkmanTaggedNativeMap,
          folkmanTaggedIsLeft, folkmanTaggedIsRight, hx]
    · by_cases hn2 : n = 2
      · subst n
        change PUnit at rel
        cases hx : args 0 <;>
          cases hy : args 1 <;>
          simp [folkmanTaggedFirstOrderStructure,
            folkmanTaggedNativeMap,
            folkmanTaggedPairingOne, hx, hy, hPair]
      · have he : IsEmpty (folkmanFirstOrderLanguage.Relations n) := by
          change IsEmpty (folkmanFirstOrderRelations n)
          simp [folkmanFirstOrderRelations, hn1, hn2]
        exact isEmptyElim rel

end SuccessorTree.NonPrecompact
