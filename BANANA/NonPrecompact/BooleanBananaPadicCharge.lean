import BANANA.NonPrecompact.BooleanBananaStoneAction
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# The space of admissible two-adic charges

A charge is finitely additive on disjoint joins, has total mass zero,
and lifts the marking modulo two. It is given the subspace topology
of the product of two-adic integer rings. The marking-preserving
automorphisms act continuously by pullback.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open Set TopologicalSpace

variable {B : Type*} [BooleanAlgebra B]

/-- The equations defining an admissible two-adic charge. -/
structure IsPadicCharge (mark : B → ZMod 2) (c : B → ℤ_[2]) : Prop where
  bot : c ⊥ = 0
  top : c ⊤ = 0
  add : ∀ a b, Disjoint a b → c (a ⊔ b) = c a + c b
  parity : ∀ a, PadicInt.toZMod (c a) = mark a

/-- The space of admissible charges, with its product subspace topology. -/
abbrev PadicCharge (mark : B → ZMod 2) := {c : B → ℤ_[2] // IsPadicCharge mark c}

private lemma isClosed_padicParity (r : ZMod 2) :
    IsClosed {x : ℤ_[2] | PadicInt.toZMod x = r} := by
  have hcast : PadicInt.toZMod (r.val : ℤ_[2]) = r := by
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hset : {x : ℤ_[2] | PadicInt.toZMod x = r} =
      {x : ℤ_[2] | ‖x - (r.val : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(1 : ℤ))} := by
    ext x
    change PadicInt.toZMod x = r ↔ ‖x - (r.val : ℤ_[2])‖ ≤ _
    have hnorm := PadicInt.norm_le_pow_iff_mem_span_pow (x - (r.val : ℤ_[2])) 1
    simp only [Nat.cast_ofNat, Nat.cast_one] at hnorm
    have hspan : IsLocalRing.maximalIdeal ℤ_[2] = Ideal.span ({2} : Set ℤ_[2]) := by
      simpa only [Nat.cast_ofNat] using PadicInt.maximalIdeal_eq_span_p (p := 2)
    rw [hnorm, pow_one, ← hspan, ← PadicInt.ker_toZMod (p := 2),
      RingHom.mem_ker, map_sub, hcast, sub_eq_zero]
  rw [hset]
  exact isClosed_le (continuous_id.sub continuous_const).norm continuous_const

/-- The equations for admissible charges cut out a closed subset of the
product of two-adic integers. -/
theorem isClosed_setOf_isPadicCharge (mark : B → ZMod 2) :
    IsClosed {c : B → ℤ_[2] | IsPadicCharge mark c} := by
  let bc : Set (B → ℤ_[2]) := {c | c ⊥ = 0}
  let tc : Set (B → ℤ_[2]) := {c | c ⊤ = 0}
  let ac : Set (B → ℤ_[2]) :=
    ⋂ a : B, ⋂ b : B, ⋂ _ : Disjoint a b, {c | c (a ⊔ b) = c a + c b}
  let pc : Set (B → ℤ_[2]) := ⋂ a : B, {c | PadicInt.toZMod (c a) = mark a}
  have hset : {c : B → ℤ_[2] | IsPadicCharge mark c} = bc ∩ tc ∩ ac ∩ pc := by
    ext c
    simp only [bc, tc, ac, pc, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨⟨⟨h.bot, h.top⟩, h.add⟩, h.parity⟩,
      fun ⟨⟨⟨hb, ht⟩, ha⟩, hp⟩ => ⟨hb, ht, ha, hp⟩⟩
  rw [hset]
  apply IsClosed.inter
  · apply IsClosed.inter
    · exact (isClosed_eq (continuous_apply ⊥) continuous_const).inter
        (isClosed_eq (continuous_apply ⊤) continuous_const)
    · exact isClosed_iInter fun a => isClosed_iInter fun b => isClosed_iInter fun _ =>
        isClosed_eq (continuous_apply (a ⊔ b)) ((continuous_apply a).add (continuous_apply b))
  · apply isClosed_iInter
    intro a
    change IsClosed ((fun c : B → ℤ_[2] => c a) ⁻¹' {x : ℤ_[2] | PadicInt.toZMod x = mark a})
    exact (isClosed_padicParity (mark a)).preimage (continuous_apply a)

instance padicCharge_compactSpace (mark : B → ZMod 2) :
    CompactSpace (PadicCharge mark) :=
  isCompact_iff_compactSpace.mp (isClosed_setOf_isPadicCharge mark).isCompact

theorem padicCharge_metrizableSpace [Countable B] (mark : B → ZMod 2) :
    MetrizableSpace (PadicCharge mark) := by
  let : SecondCountableTopology ℤ_[2] := secondCountable_of_proper
  let : SecondCountableTopology (B → ℤ_[2]) := inferInstance
  let : SecondCountableTopology (PadicCharge mark) := Subtype.secondCountableTopology _
  exact metrizableSpace_of_t3_secondCountable _

/-- Any fixed coordinate is a continuous evaluation on the charge space. -/
theorem continuous_padicChargeEvaluation (mark : B → ZMod 2) (b : B) :
    Continuous (fun c : PadicCharge mark => c.val b) :=
  (continuous_apply b).comp continuous_subtype_val

private def pullback {mark : B → ZMod 2}
    (e : B ≃o B) (he : ∀ a, mark (e a) = mark a) (c : PadicCharge mark) :
    PadicCharge mark := ⟨fun a => c.val (e a), by
  constructor
  · simpa only [map_bot] using c.property.bot
  · simpa only [map_top] using c.property.top
  · intro a b hab
    rw [map_sup]
    apply c.property.add
    rw [disjoint_iff, ← map_inf, hab.eq_bot, map_bot]
  · intro a
    exact (c.property.parity (e a)).trans (he a)⟩

instance markedAutomorphisms_padicChargeAction (mark : B → ZMod 2) :
    MulAction (markedAutomorphisms mark) (PadicCharge mark) where
  smul g c := pullback (g⁻¹).val (g⁻¹).property c
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

/-- The action on charges uses inverse evaluation on the algebra. -/
theorem padicCharge_smul_apply {mark : B → ZMod 2} (g : markedAutomorphisms mark)
    (c : PadicCharge mark) (a : B) : (g • c).val a = c.val (g.val.symm a) := rfl

instance markedAutomorphisms_padicChargeAction_continuous (mark : B → ZMod 2) :
    ContinuousSMul (markedAutomorphisms mark) (PadicCharge mark) where
  continuous_smul := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    let d (g : markedAutomorphisms mark) : WithDiscreteTopology B :=
      WithTopology.toTopology ⊥ (g.val.symm a)
    have hd : Continuous d := by
      apply continuous_discrete_rng.mpr
      intro b
      obtain ⟨x, rfl⟩ := (WithTopology.toTopology_surjective (⊥ : TopologicalSpace B)) b
      convert isOpen_markedAutomorphisms_inverseEval (mark := mark) a x using 1
      ext g
      exact (WithTopology.toTopology_injective (⊥ : TopologicalSpace B)).eq_iff
    have he : Continuous (fun p : PadicCharge mark × WithDiscreteTopology B =>
        p.1.val (WithTopology.ofTopology p.2)) :=
      continuous_prod_of_discrete_right.mpr fun b =>
        continuous_padicChargeEvaluation mark (WithTopology.ofTopology b)
    exact he.comp (continuous_snd.prodMk (hd.comp continuous_fst))

end SuccessorTree.NonPrecompact.BooleanBanana
