import BANANA.NonPrecompact.BooleanBananaPadicCharge
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Atoms
import Mathlib.Order.BooleanSubalgebra

/-!
# Nonemptiness of the two-adic charge space

On each finite algebra, lift the atom markings to two-adic integers
and correct the total on one atom. Compactness lifts this finite
solvability to the whole algebra when finite subsets lie in finite
Boolean subalgebras.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open Set
open scoped BigOperators

variable {B : Type*} [BooleanAlgebra B]

/-- Every admissible marking on a finite Boolean algebra lifts to a
two-adic charge. -/
theorem nonempty_padicCharge_of_fintype [Fintype B] [Nontrivial B] (mark : B → ZMod 2)
    (hbot : mark ⊥ = 0) (htop : mark ⊤ = 0)
    (hadd : ∀ a b, a ⊓ b = ⊥ → mark (a ⊔ b) = mark a + mark b) :
    Nonempty (PadicCharge mark) := by
  classical
  let I := {a : B // IsAtom a}
  let : Fintype I := inferInstanceAs (Fintype {a : B // IsAtom a})
  let e : B ≃o Finset I :=
    letI : CompleteAtomicBooleanAlgebra B := Fintype.toCompleteAtomicBooleanAlgebra B
    CompleteAtomicBooleanAlgebra.toSetOfIsAtom.trans Fintype.finsetOrderIsoSet.symm
  have markSum (s : Finset I) : (∑ b ∈ s, mark (e.symm {b})) = mark (e.symm s) := by
    induction s using Finset.induction_on with
    | empty =>
      change (∑ b ∈ (⊥ : Finset I), mark (e.symm {b})) = mark (e.symm ⊥)
      rw [e.symm.map_bot, hbot]
      exact Finset.sum_empty
    | @insert b s hb ih =>
      have hd : Disjoint ({b} : Finset I) s := Finset.disjoint_singleton_left.mpr hb
      have hd' : e.symm {b} ⊓ e.symm s = ⊥ := by
        rw [← e.symm.map_inf, hd.eq_bot, e.symm.map_bot]
      rw [Finset.sum_insert hb, ih]
      rw [← Finset.singleton_union, ← Finset.sup_eq_union, e.symm.map_sup, hadd _ _ hd']
  let raw (a : I) : ℤ_[2] := (mark (e.symm {a})).val
  have raw_parity (a : I) : PadicInt.toZMod (raw a) = mark (e.symm {a}) := by
    change PadicInt.toZMod ((mark (e.symm {a})).val : ℤ_[2]) = _
    rw [map_natCast, ZMod.natCast_zmod_val]
  let total := ∑ a : I, raw a
  have total_parity : PadicInt.toZMod total = 0 := by
    dsimp only [total]
    simp only [map_sum, raw_parity, markSum]
    change mark (e.symm ⊤) = 0
    rw [e.symm.map_top, htop]
  have htop_atoms : e ⊤ ≠ ∅ := by
    change e ⊤ ≠ ⊥
    rw [← e.map_bot]
    exact fun h => top_ne_bot (e.injective h)
  obtain ⟨a₀, _⟩ := Finset.nonempty_iff_ne_empty.mpr htop_atoms
  let w (b : I) : ℤ_[2] := raw b - if b = a₀ then total else 0
  refine ⟨⟨fun x => ∑ b ∈ e x, w b, ?_⟩⟩
  constructor
  · change (∑ b ∈ e ⊥, w b) = 0
    rw [e.map_bot]
    exact Finset.sum_empty
  · change (∑ b ∈ e ⊤, w b) = 0
    rw [e.map_top]
    have hsum : (∑ b : I, if b = a₀ then total else 0) = total := by
      calc
        _ = (if a₀ = a₀ then total else 0) :=
          Finset.sum_eq_single a₀ (fun b _ hb => ite_eq_right hb)
            (fun hm => (hm (Finset.mem_univ a₀)).elim)
        _ = total := ite_eq_left rfl
    change (∑ b : I, (raw b - if b = a₀ then total else 0)) = 0
    rw [Finset.sum_sub_distrib, hsum]
    exact sub_self _
  · intro x y hd
    have he : Disjoint (e x) (e y) := by
      rw [disjoint_iff, ← e.map_inf, hd.eq_bot, e.map_bot]
    change (∑ b ∈ e (x ⊔ y), w b) = _
    rw [e.map_sup, Finset.sup_eq_union, Finset.sum_union he]
  · intro x
    change PadicInt.toZMod (∑ b ∈ e x, w b) = mark x
    rw [map_sum]
    have hw (b : I) : PadicInt.toZMod (w b) = mark (e.symm {b}) := by
      by_cases hb : b = a₀ <;> simp [w, hb, raw_parity, total_parity]
    simp only [hw, markSum, e.symm_apply_apply]

private def onSubalgebra (mark : B → ZMod 2) (S : BooleanSubalgebra B) :
    Set (B → ℤ_[2]) :=
  {c | IsPadicCharge (fun a : S => mark a.val) (fun a : S => c a.val)}

private theorem isClosed_onSubalgebra (mark : B → ZMod 2) (S : BooleanSubalgebra B) :
    IsClosed (onSubalgebra mark S) :=
  (isClosed_setOf_isPadicCharge (fun a : S => mark a.val)).preimage
    (continuous_pi fun a => continuous_apply a.val)

private theorem onSubalgebra_anti (mark : B → ZMod 2) {S T : BooleanSubalgebra B}
    (h : S ≤ T) : onSubalgebra mark T ⊆ onSubalgebra mark S := by
  intro c hc
  change IsPadicCharge (fun a : T => mark a.val) (fun a : T => c a.val) at hc
  change IsPadicCharge (fun a : S => mark a.val) (fun a : S => c a.val)
  refine ⟨hc.bot, hc.top, ?_, fun a => hc.parity ⟨a.val, h a.property⟩⟩
  intro a b hab
  let x : T := ⟨a.val, h a.property⟩
  let y : T := ⟨b.val, h b.property⟩
  refine hc.add x y ?_
  rw [disjoint_iff]
  exact Subtype.ext (congrArg (Subtype.val : S → B) hab.eq_bot)

/-- If every finite family lies in a finite subalgebra, finite solvability
and compactness give a charge on the whole algebra. -/
theorem nonempty_padicCharge_of_finiteAmbient [Nontrivial B] (mark : B → ZMod 2)
    (hbot : mark ⊥ = 0) (htop : mark ⊤ = 0)
    (hadd : ∀ a b, a ⊓ b = ⊥ → mark (a ⊔ b) = mark a + mark b)
    (ambient : ∀ s : Finset B, ∃ S : BooleanSubalgebra B, Finite S ∧ (s : Set B) ⊆ S) :
    Nonempty (PadicCharge mark) := by
  classical
  let I := {S : BooleanSubalgebra B // Finite S}
  let test (S : I) : Set (B → ℤ_[2]) := onSubalgebra mark S.val
  have existsAmbient (s : Finset B) : ∃ S : I, (s : Set B) ⊆ S.val := by
    obtain ⟨S, hS, hs⟩ := ambient s
    exact ⟨⟨S, hS⟩, hs⟩
  obtain ⟨S₀, _⟩ := existsAmbient ∅
  let : Nonempty I := ⟨S₀⟩
  have hdirected : Directed (· ⊇ ·) test := by
    intro S T
    let : Finite S.val := S.property
    let : Finite T.val := T.property
    let s : Finset B := (Set.toFinite (S.val : Set B)).toFinset
    let t : Finset B := (Set.toFinite (T.val : Set B)).toFinset
    obtain ⟨U, hu⟩ := existsAmbient (s ∪ t)
    refine ⟨U, onSubalgebra_anti mark ?_, onSubalgebra_anti mark ?_⟩
    · intro x hx
      exact hu (Finset.mem_union_left _ (by simpa [s] using hx))
    · intro x hx
      exact hu (Finset.mem_union_right _ (by simpa [t] using hx))
  have hnonempty (S : I) : (test S).Nonempty := by
    let : Finite S.val := S.property
    let : Fintype S.val := Fintype.ofFinite S.val
    let : Nontrivial S.val := ⟨⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subtype.val h)⟩⟩
    obtain ⟨d⟩ := nonempty_padicCharge_of_fintype (fun a : S.val => mark a.val)
      hbot htop (fun a b h => hadd a.val b.val (congrArg Subtype.val h))
    let c (b : B) : ℤ_[2] := if hb : b ∈ S.val then d.val ⟨b, hb⟩ else 0
    refine ⟨c, ?_⟩
    have hc : (fun a : S.val => c a.val) = d.val := by
      funext a
      simp [c, a.property]
    change IsPadicCharge (fun a : S.val => mark a.val) (fun a : S.val => c a.val)
    rw [hc]
    exact d.property
  have hclosed (S : I) : IsClosed (test S) := isClosed_onSubalgebra mark S.val
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    test hdirected hnonempty (fun S => (hclosed S).isCompact) hclosed
  have localCharge (S : I) : IsPadicCharge (fun a : S.val => mark a.val)
      (fun a : S.val => c a.val) := mem_iInter.mp hc S
  refine ⟨⟨c, (localCharge S₀).bot, (localCharge S₀).top, ?_, ?_⟩⟩
  · intro a b hab
    obtain ⟨S, hs⟩ := existsAmbient {a, b}
    let x : S.val := ⟨a, hs (by simp)⟩
    let y : S.val := ⟨b, hs (by simp)⟩
    refine (localCharge S).add x y ?_
    rw [disjoint_iff]
    exact Subtype.ext hab.eq_bot
  · intro a
    obtain ⟨S, hs⟩ := existsAmbient {a}
    exact (localCharge S).parity ⟨a, hs (by simp)⟩

private theorem finiteAmbient (s : Finset B) :
    ∃ S : BooleanSubalgebra B, Finite S ∧ (s : Set B) ⊆ S := by
  classical
  let signature (u : BooleanSpectrum.Space B) (a : s) : Bool :=
    decide (u ∈ BooleanSpectrum.toSets a.val)
  let pull : BoundedLatticeHom (Set (s → Bool)) (Set (BooleanSpectrum.Space B)) :=
    { toFun := Set.preimage signature
      map_sup' := fun _ _ => rfl
      map_inf' := fun _ _ => rfl
      map_top' := rfl
      map_bot' := rfl }
  let S := (BooleanSubalgebra.map pull ⊤).comap (BooleanSpectrum.toSets (B := B))
  have hinj : Function.Injective (BooleanSpectrum.toSets (B := B)) :=
    fun _ _ h => BooleanSpectrum.clopens.injective (SetLike.coe_injective h)
  have hfin : (S : Set B).Finite := by
    change (BooleanSpectrum.toSets ⁻¹' (pull '' Set.univ)).Finite
    exact ((Set.toFinite Set.univ).image pull).preimage hinj.injOn
  refine ⟨S, hfin, ?_⟩
  intro a ha
  refine ⟨{v : s → Bool | v ⟨a, ha⟩ = true}, BooleanSubalgebra.mem_top, ?_⟩
  exact Set.ext fun _ => decide_eq_true_iff

/-- Every admissible marking of a nontrivial Boolean algebra lifts to a
two-adic charge. -/
theorem nonempty_padicCharge [Nontrivial B] (mark : B → ZMod 2)
    (hbot : mark ⊥ = 0) (htop : mark ⊤ = 0)
    (hadd : ∀ a b, a ⊓ b = ⊥ → mark (a ⊔ b) = mark a + mark b) :
    Nonempty (PadicCharge mark) :=
  nonempty_padicCharge_of_finiteAmbient mark hbot htop hadd finiteAmbient

end SuccessorTree.NonPrecompact.BooleanBanana
