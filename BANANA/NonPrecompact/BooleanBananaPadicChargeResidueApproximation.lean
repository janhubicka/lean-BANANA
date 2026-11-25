import BANANA.NonPrecompact.BooleanBananaPadicChargeExtension
import BANANA.NonPrecompact.BooleanBananaPadicChargeMinimality

/-!
# Realising finite charge residues by marked embeddings

The finite residue-partition problem is kept separate from its application
to an arbitrary homogeneous marked Boolean algebra. Once all-marked
ambients and the residue partitions exist, finite additivity transports
the required residues from atoms to every element of a finite subalgebra.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open Set
open scoped BigOperators

/-- The all-marked ambient consists of a batch and a two-atom reserve. -/
abbrev ChargeAmbientIndex (m k : ℕ) := (Fin m × Fin (2 ^ (k + 1))) ⊕ Fin 2

/-- The target consists of one atom for each batch and one final atom. -/
abbrev ChargeTargetIndex (m : ℕ) := Fin m ⊕ Unit

/-- The finite residue-realisation statement in the batch coordinates.
The owner map partitions all the ambient atoms into nonempty blocks. -/
def HasChargeResiduePartition : Prop :=
  ∀ (m k : ℕ)
    (z : ChargeAmbientIndex m k → ZMod (2 ^ (k + 1)))
    (r : ChargeTargetIndex m → ZMod (2 ^ (k + 1))),
    (∀ j, (ZMod.cast (z j) : ZMod 2) = 1) →
    (∑ j, z j) = 0 → (∑ i, r i) = 0 →
    ∃ owner : ChargeAmbientIndex m k → ChargeTargetIndex m,
      Function.Surjective owner ∧
      ∀ i, (∑ j ∈ Finset.univ.filter (fun j => owner j = i), z j) = r i

private theorem padic_residue_one :
    (PadicInt.toZModPow (p := 2) 1 : ℤ_[2] →+* ZMod 2) = PadicInt.toZMod := by
  apply ZMod.ringHom_eq_of_ker_eq
  rw [PadicInt.ker_toZModPow, pow_one, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]

private theorem padic_residue_cast (k : ℕ) (x : ℤ_[2]) :
    (ZMod.cast (PadicInt.toZModPow (k + 1) x) : ZMod 2) = PadicInt.toZMod x := by
  rw [show (ZMod.cast (PadicInt.toZModPow (k + 1) x) : ZMod 2) =
    PadicInt.toZModPow 1 x from PadicInt.cast_toZModPow 1 (k + 1) (by omega) x]
  exact congrFun (congrArg DFunLike.coe padic_residue_one) x

private noncomputable def ownerPullback {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J] [DecidableEq I]
    (owner : J → I) : BoundedLatticeHom (Finset I) (Finset J) := by
  classical
  exact {
    toFun := fun s => Finset.univ.filter (fun j => owner j ∈ s)
    map_bot' := by ext j; simp
    map_top' := by ext j; simp
    map_sup' := by intro s t; ext j; simp
    map_inf' := by intro s t; ext j; simp }

private theorem ownerPullback_injective {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (owner : J → I) (howner : Function.Surjective owner) :
    Function.Injective (ownerPullback owner) := by
  intro s t h
  ext i
  obtain ⟨j, hj⟩ := howner i
  have e := congrArg (fun q : Finset J => j ∈ q) h
  simpa [ownerPullback, hj] using e

private theorem ownerPullback_singleton {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (owner : J → I) (i : I) :
    ownerPullback owner {i} = Finset.univ.filter (fun j => owner j = i) := by
  ext j
  simp [ownerPullback]

private theorem chargeSum {S I B R : Type*} [BooleanAlgebra S] [BooleanAlgebra B]
    [Fintype I] [DecidableEq I] [Ring R]
    {mark : B → ZMod 2} (c : PadicCharge mark)
    (a : BoundedLatticeHom S B) (e : S ≃o Finset I) (rz : ℤ_[2] →+* R)
    (s : Finset I) :
    (∑ i ∈ s, rz (c.val (a (e.symm {i})))) = rz (c.val (a (e.symm s))) := by
  exact finiteAtomSum e (fun t => rz (c.val (a t))) (by rw [map_bot, c.property.bot, map_zero])
    (fun u v huv => by
      have hdisj : Disjoint (a u) (a v) := by
        rw [disjoint_iff, ← map_inf, huv.eq_bot, map_bot]
      rw [map_sup, c.property.add _ _ hdisj, map_add]) s

variable {B : Type*} [BooleanAlgebra B] [Nontrivial B]

set_option maxHeartbeats 1000000 in
/-- Every admissible charge on a homogeneous Boolean algebra having
all the requisite all-marked ambients admits all finite residue
approximations, once the finite residue partitions are available. -/
theorem exists_padicChargeResidueApproximation_of_partitions
    {mark : B → ZMod 2} (hpartition : HasChargeResiduePartition)
    (hamb : ∀ m k : ℕ,
      ∃ f : BoundedLatticeHom (Finset (ChargeAmbientIndex m k)) B,
        Function.Injective f ∧ ∀ j, mark (f {j}) = 1)
    (hhom : ∀ (S : BooleanSubalgebra B) [Fintype S]
      (f : BoundedLatticeHom S B), Function.Injective f →
        (∀ a : S, mark (f a) = mark a.val) →
        ∃ g : markedAutomorphisms mark, ∀ a : S, g.val.symm a.val = f a)
    (c d : PadicCharge mark) (F : Finset B) (k : ℕ) :
    ∃ g : markedAutomorphisms mark, ∀ b ∈ F,
      PadicInt.toZModPow (k + 1) ((g • c).val b) =
        PadicInt.toZModPow (k + 1) (d.val b) := by
  classical
  obtain ⟨S, hS, hF⟩ := finiteAmbient F
  let : Fintype S := Fintype.ofFinite S
  let I := {a : S // IsAtom a}
  let : Fintype I := inferInstanceAs (Fintype {a : S // IsAtom a})
  let e₀ : S ≃o Finset I := prebananaFiniteBooleanAtomFinsetOrderIso S
  have htop_ne_bot : (⊤ : S) ≠ ⊥ :=
    fun h => top_ne_bot (congrArg Subtype.val h)
  have hnonempty : (e₀ ⊤).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    exact htop_ne_bot (e₀.injective (h.trans e₀.map_bot.symm))
  obtain ⟨i₀, _⟩ := hnonempty
  let : Nonempty I := ⟨i₀⟩
  have hcardpos : 0 < Fintype.card I := Fintype.card_pos
  let m := Fintype.card I - 1
  have hcard : Fintype.card I = Fintype.card (ChargeTargetIndex m) := by
    simp [ChargeTargetIndex, m]
    omega
  let ei : I ≃ ChargeTargetIndex m := Fintype.equivOfCardEq hcard
  let ef : Finset I ≃o Finset (ChargeTargetIndex m) :=
    { toEquiv := ei.finsetCongr
      map_rel_iff' := Finset.map_subset_map }
  let e : S ≃o Finset (ChargeTargetIndex m) := e₀.trans ef
  obtain ⟨a, hainj, hamark⟩ := hamb m k
  let rz := PadicInt.toZModPow (p := 2) (k + 1)
  let z (j : ChargeAmbientIndex m k) := rz (c.val (a {j}))
  let r (i : ChargeTargetIndex m) := rz (d.val (e.symm {i}).val)
  have zpar (j : ChargeAmbientIndex m k) : (ZMod.cast (z j) : ZMod 2) = 1 := by
    simp only [z, rz, padic_residue_cast, c.property.parity, hamark]
  have hamass (s : Finset (ChargeAmbientIndex m k)) :
      rz (c.val (a s)) = ∑ j ∈ s, z j := by
    symm
    exact chargeSum c a (OrderIso.refl _) rz s
  have ztotal : (∑ j, z j) = 0 := by
    rw [← hamass Finset.univ, ← Finset.top_eq_univ, map_top, c.property.top, map_zero]
  have rsum (s : Finset (ChargeTargetIndex m)) :
      (∑ i ∈ s, r i) = rz (d.val (e.symm s).val) := by
    exact chargeSum d S.subtype e rz s
  have rtotal : (∑ i, r i) = 0 := by
    rw [rsum Finset.univ, ← Finset.top_eq_univ, e.symm.map_top]
    change rz (d.val ⊤) = 0
    rw [d.property.top, map_zero]
  obtain ⟨owner, hsurj, howner⟩ := hpartition m k z r zpar ztotal rtotal
  let f : BoundedLatticeHom S B :=
    a.comp ((ownerPullback owner).comp (e : BoundedLatticeHom S _))
  have hfinj : Function.Injective f :=
    hainj.comp ((ownerPullback_injective owner hsurj).comp e.injective)
  have hfatom (i : ChargeTargetIndex m) :
      rz (c.val (f (e.symm {i}))) = r i := by
    change rz (c.val (a (ownerPullback owner (e (e.symm {i}))))) = r i
    rw [e.apply_symm_apply, ownerPullback_singleton, hamass, howner]
  have hfres (x : S) : rz (c.val (f x)) = rz (d.val x.val) := by
    have hsum := chargeSum c f e rz (e x)
    rw [e.symm_apply_apply] at hsum
    calc
      rz (c.val (f x)) = ∑ i ∈ e x, rz (c.val (f (e.symm {i}))) := hsum.symm
      _ = ∑ i ∈ e x, r i := Finset.sum_congr rfl (fun i _ => hfatom i)
      _ = rz (d.val x.val) := by simpa only [e.symm_apply_apply] using rsum (e x)
  have hfmark (x : S) : mark (f x) = mark x.val := by
    have h := congrArg (fun v : ZMod (2 ^ (k + 1)) => (ZMod.cast v : ZMod 2)) (hfres x)
    simpa only [rz, padic_residue_cast, c.property.parity, d.property.parity] using h
  obtain ⟨g, hg⟩ := hhom S f hfinj hfmark
  refine ⟨g, fun b hb => ?_⟩
  let x : S := ⟨b, hF hb⟩
  rw [padicCharge_smul_apply, show g.val.symm b = f x from hg x]
  exact hfres x

/-- Under the same finite partition and homogeneity conditions, every
orbit in the two-adic charge flow is dense. -/
theorem dense_padicChargeOrbit_of_partitions {mark : B → ZMod 2}
    (hpartition : HasChargeResiduePartition)
    (hamb : ∀ m k : ℕ,
      ∃ f : BoundedLatticeHom (Finset (ChargeAmbientIndex m k)) B,
        Function.Injective f ∧ ∀ j, mark (f {j}) = 1)
    (hhom : ∀ (S : BooleanSubalgebra B) [Fintype S]
      (f : BoundedLatticeHom S B), Function.Injective f →
        (∀ a : S, mark (f a) = mark a.val) →
        ∃ g : markedAutomorphisms mark, ∀ a : S, g.val.symm a.val = f a)
    (c : PadicCharge mark) :
    Dense (MulAction.orbit (markedAutomorphisms mark) c) := by
  apply dense_padicChargeOrbit_of_finiteResidues c
  intro d F n
  obtain ⟨g, hg⟩ := exists_padicChargeResidueApproximation_of_partitions
    hpartition hamb hhom c d F n
  refine ⟨g, fun b hb => ?_⟩
  have h : n ≤ n + 1 := by omega
  rw [← PadicInt.cast_toZModPow n (n + 1) h, ← PadicInt.cast_toZModPow n (n + 1) h,
    hg b hb]

end SuccessorTree.NonPrecompact.BooleanBanana
