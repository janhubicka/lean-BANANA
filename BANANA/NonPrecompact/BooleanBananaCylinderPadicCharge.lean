import BANANA.NonPrecompact.BooleanBananaPadicChargeResiduePartition
import BANANA.NonPrecompact.PrebananaFiveAryCylinderUltrahomogeneity
import BANANA.NonPrecompact.PrebananaFiveAryCylinderFiniteAge
import BANANA.NonPrecompact.PrebananaFinitePowersetMarkedLifts
import Mathlib.Dynamics.Minimal

/-!
# The two-adic charge flow of the explicit Boolean–BANANA limit

Finite marked Boolean algebras embed into the cylinder model, and its
actual marking-preserving automorphisms extend finite marked embeddings.
The finite residue partitions therefore give dense orbits. Each orbit
is meagre, as already shown by varying the evaluation of a charge.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

/-- The actual Boolean–BANANA limit has a nonempty two-adic charge space. -/
theorem nonempty_cylinderPadicCharge :
    Nonempty (PadicCharge prebananaFiveAryCylinderMark) :=
  nonempty_padicCharge
    prebananaFiveAryCylinderMark prebananaFiveAryCylinderMark_bot
    prebananaFiveAryCylinderMark_top prebananaFiveAryCylinderMark_sup

/-- Every specified charge on a finite subalgebra extends in the actual
Boolean–BANANA limit. -/
theorem exists_cylinderPadicCharge_extension
    (S : BooleanSubalgebra PrebananaFiveAryCylinderLimitCarrier) [Fintype S]
    (d : PadicCharge (fun a : S => prebananaFiveAryCylinderMark a.val)) :
    ∃ c : PadicCharge prebananaFiveAryCylinderMark, ∀ a : S, c.val a.val = d.val a :=
  exists_padicCharge_extension
    prebananaFiveAryCylinderMark_bot prebananaFiveAryCylinderMark_top
    prebananaFiveAryCylinderMark_sup S d

private theorem cylinder_has_allMarkedAmbients (m k : ℕ) :
    ∃ f : BoundedLatticeHom (Finset (ChargeAmbientIndex m k))
      PrebananaFiveAryCylinderLimitCarrier,
      Function.Injective f ∧ ∀ j, prebananaFiveAryCylinderMark (f {j}) = 1 := by
  classical
  let I := ChargeAmbientIndex m k
  let : Nonempty I := ⟨Sum.inr 0⟩
  have heven : Even (Fintype.card I) := by
    have hp : Even (2 ^ (k+1)) := even_two.pow_of_ne_zero (Nat.succ_ne_zero k)
    simpa [I, ChargeAmbientIndex] using (Even.mul_left hp m).add even_two
  let A := prebananaFiniteMarkedPowerset I (fun _ => 1)
    (by simpa using heven.natCast_zmod_two)
  obtain ⟨f⟩ := prebananaCylinder_allFiniteModels_embed A
  refine ⟨f.hom, f.injective, fun j => ?_⟩
  let atom : Finset I := {j}
  have h := f.preserves_μ atom
  change prebananaFiveAryCylinderMark (f.hom atom) =
    ∑ _ ∈ atom, (1 : ZMod 2) at h
  rw [show (∑ _ ∈ atom, (1 : ZMod 2)) = 1 by simp [atom]] at h
  exact h

private theorem cylinder_finite_embed_extends (S : BooleanSubalgebra
    PrebananaFiveAryCylinderLimitCarrier) [Fintype S]
    (f : BoundedLatticeHom S PrebananaFiveAryCylinderLimitCarrier)
    (hf : Function.Injective f) (hm : ∀ a : S,
      prebananaFiveAryCylinderMark (f a) = prebananaFiveAryCylinderMark a.val) :
    ∃ g : markedAutomorphisms prebananaFiveAryCylinderMark,
      ∀ a : S, g.val.symm a.val = f a := by
  let A := prebananaCylinder_finiteSubmodel S
  let q : PrebananaFiniteToCountableEmbedding A prebananaCylinderCountableModel :=
    ⟨f, hf, hm⟩
  obtain ⟨E, hmark, hE⟩ := prebananaCylinder_exists_global_marked_boolean_automorphism A
    (prebananaCylinder_finiteSubmodel_embedding S) q
  let g := ofMarkedOrderIso E hmark
  refine ⟨g⁻¹, ?_⟩
  intro a
  exact hE a

/-- Finite-coordinate residues can be simultaneously approximated by an
actual marked automorphism of the cylinder model. -/
theorem exists_cylinderPadicChargeResidueApproximation
    (c d : PadicCharge prebananaFiveAryCylinderMark)
    (F : Finset PrebananaFiveAryCylinderLimitCarrier) (k : ℕ) :
    ∃ g : markedAutomorphisms prebananaFiveAryCylinderMark, ∀ b ∈ F,
      PadicInt.toZModPow (k+1) ((g • c).val b) = PadicInt.toZModPow (k+1) (d.val b) :=
  exists_padicChargeResidueApproximation_of_partitions hasChargeResiduePartition
    cylinder_has_allMarkedAmbients cylinder_finite_embed_extends c d F k

open Set

/-- Every orbit of the actual Boolean–BANANA group on the two-adic
charge space is dense and meagre, and no orbit is comeagre. -/
theorem cylinderPadicChargeOrbit_dense_meagre (c : PadicCharge prebananaFiveAryCylinderMark) :
    Dense (MulAction.orbit (markedAutomorphisms prebananaFiveAryCylinderMark) c) ∧
      IsMeagre (MulAction.orbit (markedAutomorphisms prebananaFiveAryCylinderMark) c) ∧
      MulAction.orbit (markedAutomorphisms prebananaFiveAryCylinderMark) c ∉
        residual (PadicCharge prebananaFiveAryCylinderMark) :=
  padicChargeOrbit_dense_meagre_of_homogeneous_allMarked
    cylinder_has_allMarkedAmbients cylinder_finite_embed_extends c

/-- The explicit charge flow is minimal and no orbit is comeagre. -/
theorem cylinderPadicCharge_minimal_no_comeagre :
    MulAction.IsMinimal (markedAutomorphisms prebananaFiveAryCylinderMark)
      (PadicCharge prebananaFiveAryCylinderMark) ∧
    ∀ c : PadicCharge prebananaFiveAryCylinderMark,
      MulAction.orbit (markedAutomorphisms prebananaFiveAryCylinderMark) c ∉
        residual (PadicCharge prebananaFiveAryCylinderMark) :=
  ⟨⟨fun c => (cylinderPadicChargeOrbit_dense_meagre c).1⟩,
    fun c => (cylinderPadicChargeOrbit_dense_meagre c).2.2⟩

/-- The pointwise automorphism group of the explicit Boolean–BANANA
model fails the generic point property. -/
theorem cylinderMarkedGroup_failsGenericPointProperty :
    let G := markedAutomorphisms prebananaFiveAryCylinderMark
    ¬ ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
      [MulAction G X] [ContinuousSMul G X] [MulAction.IsMinimal G X],
        ∃ x : X, MulAction.orbit G x ∈ residual X := by
  dsimp only
  intro h
  have := nonempty_cylinderPadicCharge
  have := cylinderPadicCharge_minimal_no_comeagre.1
  obtain ⟨c, hc⟩ := h (PadicCharge prebananaFiveAryCylinderMark)
  exact cylinderPadicCharge_minimal_no_comeagre.2 c hc

open scoped BigOperators Classical in
/-- Realise a zero-sum assignment of charge residues to every atom of an
arbitrary finite marked Boolean algebra by a marked cylinder embedding. -/
theorem exists_cylinderPadicChargeResidueEmbedding
    (c : PadicCharge prebananaFiveAryCylinderMark) (A : PrebananaFiniteBooleanModel)
    (k : ℕ) (r : PrebananaAbstractAtoms A.carrier → ZMod (2 ^ (k + 1)))
    (rtotal : (∑ i, r i) = 0)
    (rparity : ∀ i, (ZMod.cast (r i) : ZMod 2) = A.μ i.val) :
    ∃ f : PrebananaFiniteToCountableEmbedding A prebananaCylinderCountableModel,
      ∀ i : PrebananaAbstractAtoms A.carrier,
        PadicInt.toZModPow (k + 1) (c.val (f.hom i.val)) = r i := by
  classical
  have := prebananaAbstractAtoms_nonempty A.carrier
  obtain ⟨a, hainj, hares, hamark⟩ := exists_padicChargeResidueEmbedding_of_partitions
    hasChargeResiduePartition cylinder_has_allMarkedAmbients c k r rtotal
  let e := prebananaFiniteBooleanAtomFinsetOrderIso A.carrier
  let f := a.comp (e : BoundedLatticeHom A.carrier _)
  have hfinj : Function.Injective f := hainj.comp e.injective
  have hfmark (x : A.carrier) : prebananaFiveAryCylinderMark (f x) = A.μ x := by
    change prebananaFiveAryCylinderMark (a (e x)) = A.μ x
    rw [hamark]
    simp only [rparity]
    exact (prebananaAbstractParity_atomSum_on_atoms A.carrier A.μ A.μ_bot A.μ_add x).symm
  refine ⟨⟨f, hfinj, hfmark⟩, fun i => ?_⟩
  change PadicInt.toZModPow (k + 1) (c.val (a (e i.val))) = r i
  have hs : e i.val = {i} := by
    rw [← prebananaFiniteBoolean_singleton_represents_atom A.carrier i]
    exact e.apply_symm_apply _
  rw [hs, hares, Finset.sum_singleton]

end SuccessorTree.NonPrecompact.BooleanBanana
