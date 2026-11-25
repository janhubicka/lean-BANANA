import BANANA.NonPrecompact.FolkmanFirstOrderDecoding
import BANANA.NonPrecompact.FirstOrderPointwiseAutomorphism
import BANANA.NonPrecompact.FolkmanBooleanInterval
import BANANA.NonPrecompact.BooleanBananaStoneAction
import BANANA.NonPrecompact.BooleanStoneNonamenabilityAbstract
import BANANA.NonPrecompact.OpenSubgroupAmenability
import BANANA.NonPrecompact.FolkmanAtomCode
import Mathlib.Algebra.Group.Action.Hom

/-!
# Stone action of an interval stabilizer in a Folkman structure

The first-order automorphism group acts on each sort as a non-unital
ring automorphism. The open subgroup fixing a nonzero left element
acts on the unital Boolean interval below it, and hence on the compact
Stone space of that interval. Transitivity on its proper nonzero
elements is incompatible with invariant probability once a three-atom
subalgebra is present.
-/

namespace SuccessorTree.NonPrecompact.FolkmanDecoding

open FirstOrder CategoryTheory MeasureTheory BooleanBanana
open scoped FirstOrder

variable (M : Bundled.{0} folkmanLanguage.Structure)
variable (hD : FactorsThroughPairedProducts M)

private theorem left_idempotent (x : leftSort M hD) : x * x = x :=
  Subtype.ext (productRing_mul_self M hD x.val)

/-- The subgroup fixing the chosen left element is open in the topology of
pointwise convergence on the encoded structure. -/
def leftIntervalStabilizer (a : leftSort M hD) :
    Subgroup (FirstOrderAut folkmanLanguage M) where
  carrier := {g | g.toEquiv a.val = a.val}
  one_mem' := rfl
  mul_mem' := fun {g h} hg hh => by
    change g.toEquiv a.val = a.val at hg
    change h.toEquiv a.val = a.val at hh
    change g.toEquiv (h.toEquiv a.val) = a.val
    rw [hh, hg]
  inv_mem' := fun {g} hg => by
    change g.toEquiv.symm a.val = a.val
    simpa only [Language.Equiv.symm_apply_apply] using
      (congrArg g.toEquiv.symm hg).symm

theorem leftIntervalStabilizer_isOpen (a : leftSort M hD) :
    IsOpen (leftIntervalStabilizer M hD a : Set (FirstOrderAut folkmanLanguage M)) :=
  FirstOrderAut.isOpen_eval a.val a.val

private abbrev I (a : leftSort M hD) := folkmanBooleanInterval a

local instance interval_ring (a : leftSort M hD) : BooleanRing (I M hD a) :=
  folkmanIntervalBooleanRing (left_idempotent M hD) a

/-- The unital Boolean algebra below the chosen left element. -/
abbrev LeftIntervalAlgebra (a : leftSort M hD) := AsBoolAlg (I M hD a)

private def intervalOrderIso (a : leftSort M hD) (g : leftIntervalStabilizer M hD a) :
    LeftIntervalAlgebra M hD a ≃o LeftIntervalAlgebra M hD a := by
  let e := leftSortRingEquivOf M hD g.val.toEquiv
  have ha : e a = a := Subtype.ext g.property
  let r := folkmanIntervalRingEquiv a e ha
  refine {
    toEquiv := ofBoolAlg.trans (r.toEquiv.trans toBoolAlg)
    map_rel_iff' := ?_ }
  intro x y
  rw [← ofBoolAlg_mul_ofBoolAlg_eq_left_iff, ← ofBoolAlg_mul_ofBoolAlg_eq_left_iff]
  change r (ofBoolAlg x) * r (ofBoolAlg y) = r (ofBoolAlg x) ↔ _
  rw [← map_mul]
  exact r.injective.eq_iff

private def intervalValue (a : leftSort M hD) (x : LeftIntervalAlgebra M hD a) : M :=
  (ofBoolAlg x).val.val

private theorem intervalValue_injective (a : leftSort M hD) :
    Function.Injective (intervalValue M hD a) := fun _ _ h =>
  ofBoolAlg.injective (Subtype.ext (Subtype.ext h))

private theorem intervalOrderIso_value (a : leftSort M hD)
    (g : leftIntervalStabilizer M hD a) (x : LeftIntervalAlgebra M hD a) :
    intervalValue M hD a (intervalOrderIso M hD a g x) =
      g.val.toEquiv (intervalValue M hD a x) := rfl

private def intervalAutHom (a : leftSort M hD) :
    leftIntervalStabilizer M hD a →* markedAutomorphisms (fun _ : LeftIntervalAlgebra M hD a => ()) where
  toFun g := ofMarkedOrderIso (intervalOrderIso M hD a g) (fun _ => rfl)
  map_one' := by
    apply Subtype.ext
    ext x
    apply intervalValue_injective M hD a
    exact rfl
  map_mul' g h := by
    apply Subtype.ext
    ext x
    apply intervalValue_injective M hD a
    exact rfl

private theorem continuous_intervalAutHom (a : leftSort M hD) :
    Continuous (intervalAutHom M hD a) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  apply continuous_discrete_rng.mpr
  intro y
  obtain ⟨y, rfl⟩ := (WithTopology.toTopology_surjective (⊥ : TopologicalSpace (LeftIntervalAlgebra M hD a))) y
  have ho : IsOpen {g : leftIntervalStabilizer M hD a |
      g.val.toEquiv (intervalValue M hD a x) = intervalValue M hD a y} :=
    (FirstOrderAut.isOpen_eval _ _).preimage continuous_subtype_val
  convert ho using 1
  ext g
  change WithTopology.toTopology (⊥ : TopologicalSpace (LeftIntervalAlgebra M hD a))
      (intervalOrderIso M hD a g x) = WithTopology.toTopology ⊥ y ↔ _
  rw [(WithTopology.toTopology_injective (⊥ : TopologicalSpace (LeftIntervalAlgebra M hD a))).eq_iff]
  exact (intervalValue_injective M hD a).eq_iff.symm

/-- An actual three-atom subring with unit a gives a bounded-lattice
embedding into the Boolean interval below a. -/
def intervalThreeAtomLatticeHom (a : leftSort M hD)
    (f : FolkmanNativeCodeRing 3 →ₙ+* leftSort M hD) (hf : f 1 = a) :
    BoundedLatticeHom (Finset (Fin 3)) (LeftIntervalAlgebra M hD a) :=
  (folkmanHomIntoInterval (left_idempotent M hD) a f hf).asBoolAlg.comp
    (OrderIso.asBoolAlgAsBoolRing (Finset (Fin 3))).symm

/-- If the stabilizer moves every proper nonzero element of the interval
to every other such element, the three-atom obstruction implies
nonamenability of the full pointwise automorphism group. -/
theorem not_amenable_of_leftInterval
    (a : leftSort M hD) (ha : a ≠ 0)
    (htrans : ∀ x y : leftSort M hD,
      x ≠ 0 → x ≠ a → x*a=x → y ≠ 0 → y ≠ a → y*a=y →
      ∃ e : M ≃[folkmanLanguage] M, e a.val = a.val ∧ e x.val = y.val)
    (f : FolkmanNativeCodeRing 3 →ₙ+* leftSort M hD) (hfinj : Function.Injective f) (hf : f 1 = a) :
    ¬ IsTopologicallyAmenable (FirstOrderAut folkmanLanguage M) := by
  classical
  intro hAmen
  let G := leftIntervalStabilizer M hD a
  have hG : IsTopologicallyAmenable G :=
    isTopologicallyAmenable_openSubgroup _ (leftIntervalStabilizer_isOpen M hD a) hAmen
  let B := LeftIntervalAlgebra M hD a
  let ρ := intervalAutHom M hD a
  letI : Nontrivial B := ⟨⟨⊤, ⊥, fun h => ha (Subtype.ext (congrArg (intervalValue M hD a) h))⟩⟩
  have htr (x y : B) (hx0 : x ≠ ⊥) (hx1 : x ≠ ⊤) (hy0 : y ≠ ⊥) (hy1 : y ≠ ⊤) :
      ∃ g : G, (ρ g).val x = y := by
    let x' : I M hD a := ofBoolAlg x
    let y' : I M hD a := ofBoolAlg y
    have hx0' : x'.val ≠ 0 := fun h => hx0 (ofBoolAlg.injective (Subtype.ext h))
    have hxa : x'.val ≠ a := fun h => hx1 (ofBoolAlg.injective (Subtype.ext h))
    have hy0' : y'.val ≠ 0 := fun h => hy0 (ofBoolAlg.injective (Subtype.ext h))
    have hya : y'.val ≠ a := fun h => hy1 (ofBoolAlg.injective (Subtype.ext h))
    obtain ⟨e, heA, heX⟩ := htrans x'.val y'.val hx0' hxa x'.property hy0' hya y'.property
    let g : G := ⟨FirstOrderAut.ofEquiv e, heA⟩
    refine ⟨g, intervalValue_injective M hD a ?_⟩
    exact heX
  let f' := intervalThreeAtomLatticeHom M hD a f hf
  have hfinj' : Function.Injective f' := by
    intro x y h
    apply toBoolRing.injective
    apply hfinj
    exact congrArg (fun x : B => (ofBoolAlg x).val) h
  exact (not_amenable_of_transitiveBooleanHom ρ (continuous_intervalAutHom M hD a)
      htr f' hfinj') hG

end SuccessorTree.NonPrecompact.FolkmanDecoding
