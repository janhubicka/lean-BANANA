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

variable {B : Type*} [BooleanAlgebra B]

/-- Arbitrary zero-sum residues on a nonempty set of target atoms are
realised by a Boolean embedding of the target powerset. -/
theorem exists_padicChargeResidueEmbedding_of_partitions {mark : B → ZMod 2}
    (hpartition : HasChargeResiduePartition)
    (hamb : ∀ m k : ℕ,
      ∃ f : BoundedLatticeHom (Finset (ChargeAmbientIndex m k)) B,
        Function.Injective f ∧ ∀ j, mark (f {j}) = 1)
    (c : PadicCharge mark) (k : ℕ) {I : Type*} [Fintype I] [Nonempty I] [DecidableEq I]
    (r : I → ZMod (2 ^ (k + 1))) (rtotal : (∑ i, r i) = 0) :
    ∃ f : BoundedLatticeHom (Finset I) B, Function.Injective f ∧
      (∀ s : Finset I, PadicInt.toZModPow (k + 1) (c.val (f s)) = ∑ i ∈ s, r i) ∧
      ∀ s : Finset I, mark (f s) = ∑ i ∈ s, (ZMod.cast (r i) : ZMod 2) := by
  classical
  have hcardpos : 0 < Fintype.card I := Fintype.card_pos
  let m := Fintype.card I - 1
  have hcard : Fintype.card I = Fintype.card (ChargeTargetIndex m) := by
    simp [ChargeTargetIndex, m]
    omega
  let e : I ≃ ChargeTargetIndex m := Fintype.equivOfCardEq hcard
  let ef : Finset I ≃o Finset (ChargeTargetIndex m) :=
    { toEquiv := e.finsetCongr
      map_rel_iff' := Finset.map_subset_map }
  let rr (i : ChargeTargetIndex m) := r (e.symm i)
  have rrtotal : (∑ i, rr i) = 0 := by
    rw [← Equiv.sum_comp e rr]
    simpa [rr] using rtotal
  obtain ⟨a, hainj, hamark⟩ := hamb m k
  let rz := PadicInt.toZModPow (p := 2) (k + 1)
  let z (j : ChargeAmbientIndex m k) := rz (c.val (a {j}))
  have zpar (j : ChargeAmbientIndex m k) : (ZMod.cast (z j) : ZMod 2) = 1 := by
    simp only [z, rz, padic_residue_cast, c.property.parity, hamark]
  have hamass (s : Finset (ChargeAmbientIndex m k)) :
      rz (c.val (a s)) = ∑ j ∈ s, z j :=
    (chargeSum c a (OrderIso.refl _) rz s).symm
  have ztotal : (∑ j, z j) = 0 := by
    rw [← hamass Finset.univ, ← Finset.top_eq_univ, map_top, c.property.top, map_zero]
  obtain ⟨owner, hsurj, howner⟩ := hpartition m k z rr zpar ztotal rrtotal
  let f : BoundedLatticeHom (Finset I) B :=
    a.comp ((ownerPullback owner).comp (ef : BoundedLatticeHom (Finset I) _))
  have hfinj : Function.Injective f :=
    hainj.comp ((ownerPullback_injective owner hsurj).comp ef.injective)
  have hfatom (i : I) : rz (c.val (f {i})) = r i := by
    change rz (c.val (a (ownerPullback owner (ef {i})))) = r i
    have hs : ef {i} = {e i} := by
      change ({i} : Finset I).map e.toEmbedding = {e i}
      exact Finset.map_singleton _ _
    rw [hs, ownerPullback_singleton, hamass, howner]
    simp [rr]
  have hfres (s : Finset I) : rz (c.val (f s)) = ∑ i ∈ s, r i := by
    calc
      _ = ∑ i ∈ s, rz (c.val (f {i})) := (chargeSum c f (OrderIso.refl _) rz s).symm
      _ = _ := Finset.sum_congr rfl (fun i _ => hfatom i)
  refine ⟨f, hfinj, hfres, fun s => ?_⟩
  let reduce := ZMod.castHom (dvd_pow_self 2 (Nat.succ_ne_zero k)) (ZMod 2)
  have h := congrArg reduce (hfres s)
  rw [map_sum] at h
  simpa only [reduce, rz, ZMod.castHom_apply, padic_residue_cast, c.property.parity] using h

variable [Nontrivial B]

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
  let rz := PadicInt.toZModPow (p := 2) (k + 1)
  let r (i : I) := rz (d.val (e₀.symm {i}).val)
  have rsum (s : Finset I) :
      (∑ i ∈ s, r i) = rz (d.val (e₀.symm s).val) := by
    exact chargeSum d S.subtype e₀ rz s
  have rtotal : (∑ i, r i) = 0 := by
    rw [rsum Finset.univ, ← Finset.top_eq_univ, e₀.symm.map_top]
    change rz (d.val ⊤) = 0
    rw [d.property.top, map_zero]
  obtain ⟨a, hainj, hares, _⟩ :=
    exists_padicChargeResidueEmbedding_of_partitions hpartition hamb c k r rtotal
  let f := a.comp (e₀ : BoundedLatticeHom S (Finset I))
  have hfinj : Function.Injective f := hainj.comp e₀.injective
  have hfres (x : S) : rz (c.val (f x)) = rz (d.val x.val) := by
    change rz (c.val (a (e₀ x))) = rz (d.val x.val)
    rw [hares, rsum, e₀.symm_apply_apply]
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
