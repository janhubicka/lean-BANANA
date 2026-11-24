import BANANA.NonPrecompact.BooleanSpectrum
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Order.Group.End
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.MulAction

/-!
# Pointwise automorphisms and their Stone action

The automorphisms of a marked Boolean algebra are the order-preserving
permutations preserving its marking. They have the topology of pointwise
convergence on the discrete algebra and act continuously on its Stone space.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open TopologicalSpace

variable {B T : Type*} [BooleanAlgebra B]

/-- The subgroup of Boolean automorphisms preserving the marking. -/
def markedAutomorphisms (mark : B → T) : Subgroup (B ≃o B) where
  carrier := {e | ∀ a, mark (e a) = mark a}
  one_mem' := fun _ => rfl
  mul_mem' := fun he hf a => (he _).trans (hf a)
  inv_mem' := by
    intro e he a
    change mark (e.symm a) = mark a
    simpa only [OrderIso.apply_symm_apply] using (he (e.symm a)).symm

/-- A marking-preserving order isomorphism belongs to the full automorphism group. -/
def ofMarkedOrderIso {mark : B → T} (e : B ≃o B) (h : ∀ a, mark (e a) = mark a) :
    markedAutomorphisms mark :=
  ⟨e, h⟩

instance markedAutomorphisms_mulAction (mark : B → T) : MulAction (markedAutomorphisms mark) B where
  smul g a := g.val a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

private def discreteValue (a : B) : WithDiscreteTopology B := WithTopology.toTopology ⊥ a

private def pointwiseEvaluation {mark : B → T} (g : markedAutomorphisms mark) :
    B → WithDiscreteTopology B :=
  fun a => discreteValue (g.val a)

/-- The pointwise topology is the subspace topology from the product
of copies of the discrete Boolean algebra. -/
instance markedAutomorphisms_pointwiseTopology (mark : B → T) :
    TopologicalSpace (markedAutomorphisms mark) :=
  .induced pointwiseEvaluation inferInstance

private theorem continuous_pointwiseEvaluation {mark : B → T} :
    Continuous (pointwiseEvaluation (mark := mark)) :=
  continuous_induced_dom

theorem isOpen_markedAutomorphisms_eval {mark : B → T} (a b : B) :
    IsOpen {g : markedAutomorphisms mark | g.val a = b} := by
  convert (isOpen_discrete ({discreteValue b} : Set (WithDiscreteTopology B))).preimage
    ((continuous_apply a).comp (continuous_pointwiseEvaluation (mark := mark))) using 1
  ext g
  exact (WithTopology.toTopology_injective (⊥ : TopologicalSpace B)).eq_iff.symm

theorem isOpen_markedAutomorphisms_inverseEval {mark : B → T} (a b : B) :
    IsOpen {g : markedAutomorphisms mark | g.val.symm a = b} := by
  convert isOpen_markedAutomorphisms_eval (mark := mark) b a using 1
  ext g
  exact (g.val.toEquiv.symm_apply_eq).trans eq_comm

instance markedAutomorphisms_topologicalGroup (mark : B → T) :
    IsTopologicalGroup (markedAutomorphisms mark) where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    apply continuous_discrete_rng.mpr
    intro b
    obtain ⟨b, rfl⟩ := (WithTopology.toTopology_surjective (⊥ : TopologicalSpace B)) b
    have hfib :
        (fun p : markedAutomorphisms mark × markedAutomorphisms mark =>
          pointwiseEvaluation (p.1 * p.2) a) ⁻¹' {discreteValue b} =
        ⋃ c : B, {g : markedAutomorphisms mark | g.val c = b} ×ˢ
          {g : markedAutomorphisms mark | g.val a = c} := by
      ext p
      change discreteValue (p.1.val (p.2.val a)) = discreteValue b ↔ _
      rw [(WithTopology.toTopology_injective (⊥ : TopologicalSpace B)).eq_iff]
      simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨p.2.val a, h, rfl⟩, fun ⟨c, hc, hc'⟩ => hc' ▸ hc⟩
    change IsOpen ((fun p : markedAutomorphisms mark × markedAutomorphisms mark =>
      pointwiseEvaluation (p.1 * p.2) a) ⁻¹' {discreteValue b})
    rw [hfib]
    exact isOpen_iUnion fun c =>
      (isOpen_markedAutomorphisms_eval c b).prod (isOpen_markedAutomorphisms_eval a c)
  continuous_inv := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    apply continuous_discrete_rng.mpr
    intro b
    obtain ⟨b, rfl⟩ := (WithTopology.toTopology_surjective (⊥ : TopologicalSpace B)) b
    convert isOpen_markedAutomorphisms_inverseEval (mark := mark) a b using 1
    ext g
    exact (WithTopology.toTopology_injective (⊥ : TopologicalSpace B)).eq_iff

private theorem spectrum_eq_of_mem_clopens {x y : BooleanSpectrum.Space B}
    (h : ∀ a : B, x ∈ (BooleanSpectrum.clopens a : Set (BooleanSpectrum.Space B)) ↔
      y ∈ (BooleanSpectrum.clopens a : Set (BooleanSpectrum.Space B))) : x = y := by
  apply PrimeSpectrum.ext
  ext r
  have hr := h (ofBoolRing r)
  simp only [BooleanSpectrum.coe_clopens, toBoolRing_ofBoolRing] at hr
  have hn := (PrimeSpectrum.mem_basicOpen r x).symm.trans
    (hr.trans (PrimeSpectrum.mem_basicOpen r y))
  simpa only [Classical.not_not] using not_congr hn

private theorem homeomorph_mem_clopens {mark : B → T}
    (g : markedAutomorphisms mark) (x : BooleanSpectrum.Space B) (b : B) :
    BooleanSpectrum.homeomorph g.val x ∈
      (BooleanSpectrum.clopens b : Set (BooleanSpectrum.Space B)) ↔
      x ∈ (BooleanSpectrum.clopens (g.val.symm b) : Set (BooleanSpectrum.Space B)) := by
  change x ∈ BooleanSpectrum.homeomorph g.val ⁻¹'
    (BooleanSpectrum.clopens b : Set (BooleanSpectrum.Space B)) ↔ _
  rw [BooleanSpectrum.preimage_homeomorph_clopens]

/-- The marking-preserving automorphisms act by their induced Stone homeomorphisms. -/
noncomputable instance markedAutomorphisms_stoneAction (mark : B → T) :
    MulAction (markedAutomorphisms mark) (BooleanSpectrum.Space B) where
  smul g x := BooleanSpectrum.homeomorph g.val x
  one_smul x := by
    apply spectrum_eq_of_mem_clopens
    intro b
    exact homeomorph_mem_clopens 1 x b
  mul_smul g h x := by
    apply spectrum_eq_of_mem_clopens
    intro b
    exact (homeomorph_mem_clopens (g * h) x b).trans
      (((homeomorph_mem_clopens g _ b).trans (homeomorph_mem_clopens h x _)).symm)

theorem stoneAction_preimage_clopens {mark : B → T}
    (g : markedAutomorphisms mark) (b : B) :
    (fun x : BooleanSpectrum.Space B => g • x) ⁻¹'
      (BooleanSpectrum.clopens b : Set (BooleanSpectrum.Space B)) =
      BooleanSpectrum.clopens (g.val.symm b) := by
  exact Set.ext fun x => homeomorph_mem_clopens g x b

instance markedAutomorphisms_stoneAction_continuous (mark : B → T) :
    ContinuousSMul (markedAutomorphisms mark) (BooleanSpectrum.Space B) where
  continuous_smul :=
    BooleanSpectrum.continuous_homeomorph (fun g : markedAutomorphisms mark => g.val)
      (isOpen_markedAutomorphisms_inverseEval (mark := mark))

end SuccessorTree.NonPrecompact.BooleanBanana
