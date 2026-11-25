import BANANA.NonPrecompact.BooleanBananaPadicChargeNonempty
import BANANA.NonPrecompact.BooleanBananaPadicChargeOrbit

/-!
# Extension of a prescribed two-adic charge

Correct a pre-existing global charge by a linear combination of Stone point
masses, one point chosen in every atom of the finite subalgebra. All
coefficients reduce to zero modulo two and their sum is zero.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open Set
open scoped BigOperators

/-- A disjoint-additive function on a finite Boolean algebra is the sum of its atom values. -/
theorem finiteAtomSum {S I V : Type*}
    [BooleanAlgebra S] [Fintype I] [DecidableEq I] [AddCommMonoid V]
    (e : S ≃o Finset I) (f : S → V)
    (hbot : f ⊥ = 0) (hadd : ∀ a b, Disjoint a b → f (a ⊔ b) = f a + f b)
    (s : Finset I) :
    ∑ i ∈ s, f (e.symm {i}) = f (e.symm s) := by
  induction s using Finset.induction_on with
  | empty =>
    change (∑ i ∈ (⊥ : Finset I), f (e.symm {i})) = f (e.symm ⊥)
    rw [e.symm.map_bot, hbot]
    exact Finset.sum_empty
  | @insert i s hi ih =>
    have hd : Disjoint ({i} : Finset I) s :=
      Finset.disjoint_singleton_left.mpr hi
    have hd' : Disjoint (e.symm {i}) (e.symm s) := by
      rw [disjoint_iff, ← e.symm.map_inf, hd.eq_bot, e.symm.map_bot]
    rw [Finset.sum_insert hi, ih, ← Finset.singleton_union, ← Finset.sup_eq_union,
      e.symm.map_sup, hadd _ _ hd']

variable {B : Type*} [BooleanAlgebra B]

/-- Any charge on a finite Boolean subalgebra extends to the whole
algebra whenever a global charge exists. -/
theorem exists_padicCharge_extension_of_global {mark : B → ZMod 2}
    (c : PadicCharge mark) (S : BooleanSubalgebra B) [Fintype S]
    (d : PadicCharge (fun a : S => mark a.val)) :
    ∃ c' : PadicCharge mark, ∀ a : S, c'.val a.val = d.val a := by
  classical
  let I := {a : S // IsAtom a}
  let : Fintype I := inferInstanceAs (Fintype {a : S // IsAtom a})
  let e : S ≃o Finset I :=
    letI : CompleteAtomicBooleanAlgebra S := Fintype.toCompleteAtomicBooleanAlgebra S
    CompleteAtomicBooleanAlgebra.toSetOfIsAtom.trans Fintype.finsetOrderIsoSet.symm
  let atom (i : I) : B := (e.symm {i}).val
  have atom_ne_bot (i : I) : atom i ≠ ⊥ := by
    intro h
    have h' : e.symm {i} = ⊥ := Subtype.ext h
    exact Finset.singleton_ne_empty i (e.symm.injective ((e.symm.map_bot).symm ▸ h'))
  have hexists (i : I) : ∃ u : BooleanSpectrum.Space B, u ∈ BooleanSpectrum.toSets (atom i) := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro h
    apply atom_ne_bot i
    have hinj : Function.Injective (BooleanSpectrum.toSets (B := B)) :=
      fun _ _ he => BooleanSpectrum.clopens.injective (SetLike.coe_injective he)
    apply hinj
    rw [map_bot]
    exact h
  choose u hu using hexists
  have point_eval (i : I) (s : Finset I) :
      pointMass (u i) (e.symm s).val = if i ∈ s then 1 else 0 := by
    by_cases hi : i ∈ s
    · have hle : e.symm {i} ≤ e.symm s :=
        e.symm.monotone (Finset.singleton_subset_iff.mpr hi)
      have hle' : atom i ≤ (e.symm s).val := hle
      have hset : BooleanSpectrum.toSets (atom i) ⊓
          BooleanSpectrum.toSets (e.symm s).val = BooleanSpectrum.toSets (atom i) := by
        rw [← map_inf, inf_eq_left.mpr hle']
      have hmem : u i ∈ BooleanSpectrum.toSets (e.symm s).val :=
        (show u i ∈ BooleanSpectrum.toSets (atom i) ⊓
          BooleanSpectrum.toSets (e.symm s).val from hset.symm ▸ hu i).2
      simp only [pointMass, ite_eq_left hmem, ite_eq_left hi]
    · have hd : Disjoint ({i} : Finset I) s := Finset.disjoint_singleton_left.mpr hi
      have hd' : Disjoint (atom i) (e.symm s).val := by
        rw [disjoint_iff]
        have hmeet : e.symm {i} ⊓ e.symm s = (⊥ : S) := by
          rw [← e.symm.map_inf, hd.eq_bot, e.symm.map_bot]
        exact congrArg Subtype.val hmeet
      have hds : Disjoint (BooleanSpectrum.toSets (atom i))
          (BooleanSpectrum.toSets (e.symm s).val) := by
        rw [disjoint_iff, ← map_inf, hd'.eq_bot, map_bot]
      have hn : u i ∉ BooleanSpectrum.toSets (e.symm s).val :=
        fun hm => Set.disjoint_left.mp hds (hu i) hm
      simp only [pointMass, ite_eq_right hn, ite_eq_right hi]
  let w (i : I) : ℤ_[2] := d.val (e.symm {i}) - c.val (atom i)
  have w_parity (i : I) : PadicInt.toZMod (w i) = 0 := by
    simp only [w, map_sub, d.property.parity, c.property.parity, atom, sub_self]
  have sum_eq (a : S) :
      (∑ i ∈ e a, w i) = d.val a - c.val a.val := by
    have h₁ := finiteAtomSum e d.val d.property.bot d.property.add (e a)
    have h₂ := finiteAtomSum e (fun a : S => c.val a.val) c.property.bot
      (fun a b hab => c.property.add a.val b.val
        (disjoint_iff.mpr (congrArg Subtype.val hab.eq_bot))) (e a)
    simp only [e.symm_apply_apply] at h₁ h₂
    simp only [w, atom, Finset.sum_sub_distrib, h₁, h₂]
  have sum_zero : (∑ i : I, w i) = 0 := by
    have h := sum_eq ⊤
    rw [e.map_top, d.property.top] at h
    change (∑ i : I, w i) = 0 - c.val ⊤ at h
    rw [c.property.top, sub_zero] at h
    exact h
  let correction (b : B) : ℤ_[2] := ∑ i : I, w i * pointMass (u i) b
  refine ⟨⟨fun b => c.val b + correction b, ?_⟩, ?_⟩
  · constructor
    · simp only [correction, pointMass, map_bot, Set.bot_eq_empty,
        Set.mem_empty_iff_false, ite_false, mul_zero, Finset.sum_const_zero,
        c.property.bot, add_zero]
    · simp only [correction, pointMass, map_top, Set.top_eq_univ,
        Set.mem_univ, ite_true, mul_one, sum_zero, c.property.top, add_zero]
    · intro a b hab
      simp only [correction, c.property.add a b hab,
        pointMass_add _ _ _ hab, mul_add, Finset.sum_add_distrib]
      abel
    · intro b
      simp only [map_add, c.property.parity, correction, map_sum, map_mul, w_parity,
        zero_mul, Finset.sum_const_zero, add_zero]
  · intro a
    change c.val a.val + correction a.val = d.val a
    have heval (i : I) : pointMass (u i) a.val = if i ∈ e a then 1 else 0 := by
      simpa only [e.symm_apply_apply] using point_eval i (e a)
    have hsum : correction a.val = ∑ i ∈ e a, w i := by
      simp only [correction, heval, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp
    rw [hsum, sum_eq]
    abel

/-- Any charge on a finite subalgebra of an admissibly marked Boolean
algebra extends to an actual global charge. -/
theorem exists_padicCharge_extension [Nontrivial B] {mark : B → ZMod 2}
    (hbot : mark ⊥ = 0) (htop : mark ⊤ = 0)
    (hadd : ∀ a b, a ⊓ b = ⊥ → mark (a ⊔ b) = mark a + mark b)
    (S : BooleanSubalgebra B) [Fintype S]
    (d : PadicCharge (fun a : S => mark a.val)) :
    ∃ c' : PadicCharge mark, ∀ a : S, c'.val a.val = d.val a := by
  obtain ⟨c⟩ := nonempty_padicCharge mark hbot htop hadd
  exact exists_padicCharge_extension_of_global c S d

end SuccessorTree.NonPrecompact.BooleanBanana
