import BANANA.NonPrecompact.FolkmanFirstOrderDecoding
import BANANA.NonPrecompact.FirstOrderPointwiseAutomorphism
import BANANA.NonPrecompact.TopologicalAmenability
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Group.Action.Hom

/-!
# The native topological automorphism group of a paired ring

A native automorphism is a pair of non-unital ring automorphisms
preserving the cross-pairing. The topology is pointwise convergence on
both discrete ring sorts. Re-encoding gives a continuous surjective
homomorphism to the first-order automorphism group.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder CategoryTheory BooleanBanana MeasureTheory
open scoped FirstOrder

section General

variable {L R : Type} [NonUnitalRing L] [NonUnitalRing R]
variable (p : L → R → ZMod 2)

/-- Pairing-preserving automorphisms of the two original ring sorts. -/
def folkmanPairedAutomorphisms : Subgroup (RingAut L × RingAut R) where
  carrier := {g | ∀ x y, p (g.1 x) (g.2 y) = p x y}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun hg hh x y => (hg _ _).trans (hh _ _)
  inv_mem' := fun {g} hg x y => by
    change p (g.1.symm x) (g.2.symm y) = p x y
    simpa only [RingEquiv.apply_symm_apply] using (hg (g.1.symm x) (g.2.symm y)).symm

private def pairedEvaluation (g : folkmanPairedAutomorphisms p) :
    (L → WithDiscreteTopology L) × (R → WithDiscreteTopology R) :=
  (fun x => WithTopology.toTopology ⊥ (g.val.1 x),
   fun y => WithTopology.toTopology ⊥ (g.val.2 y))

/-- The native pointwise topology on the two ring sorts. -/
instance : TopologicalSpace (folkmanPairedAutomorphisms p) :=
  .induced (pairedEvaluation p) inferInstance

private def productLanguageEquiv (g : folkmanPairedAutomorphisms p) :
    letI := folkmanProductStructure p
    (L × R) ≃[folkmanLanguage] (L × R) := by
  letI := folkmanProductStructure p
  let f := folkmanProductEmbedding p p g.val.1.toNonUnitalRingHom g.val.2.toNonUnitalRingHom
    g.val.1.injective g.val.2.injective g.property
  exact {
    toEquiv := g.val.1.toEquiv.prodCongr g.val.2.toEquiv
    map_fun' := f.map_fun'
    map_rel' := f.map_rel' }

private theorem productLanguageEquiv_apply (g : folkmanPairedAutomorphisms p) (x : L × R) :
    letI := folkmanProductStructure p
    productLanguageEquiv p g x = (g.val.1 x.1, g.val.2 x.2) := rfl

variable {M : Type} [folkmanLanguage.Structure M]

/-- Re-encoding native automorphisms gives actual first-order automorphisms. -/
def nativePairedToEncoded (c : letI := folkmanProductStructure p;
    M ≃[folkmanLanguage] (L × R)) :
    folkmanPairedAutomorphisms p →* FirstOrderAut folkmanLanguage M := by
  letI := folkmanProductStructure p
  refine {
    toFun := fun g => FirstOrderAut.ofEquiv ((c.symm.comp (productLanguageEquiv p g)).comp c)
    map_one' := ?_
    map_mul' := ?_ }
  · change _ = Language.Equiv.refl _ _
    apply Language.Equiv.ext
    intro x
    exact c.symm_apply_apply x
  · intro g h
    apply Language.Equiv.ext
    intro x
    change c.symm (g.val.1 (h.val.1 (c x).1), g.val.2 (h.val.2 (c x).2)) =
      c.symm (g.val.1 (c (c.symm (h.val.1 (c x).1, h.val.2 (c x).2))).1,
        g.val.2 (c (c.symm (h.val.1 (c x).1, h.val.2 (c x).2))).2)
    rw [c.apply_symm_apply]

theorem nativePairedToEncoded_apply (c : letI := folkmanProductStructure p;
    M ≃[folkmanLanguage] (L × R)) (g : folkmanPairedAutomorphisms p) (x : M) :
    letI := folkmanProductStructure p
    (nativePairedToEncoded p c g).toEquiv x =
      c.symm (g.val.1 (c x).1, g.val.2 (c x).2) := rfl

theorem nativePairedToEncoded_surjective (c : letI := folkmanProductStructure p;
    M ≃[folkmanLanguage] (L × R)) :
    Function.Surjective (nativePairedToEncoded p c) := by
  letI := folkmanProductStructure p
  intro g
  let q := (c.comp g.toEquiv).comp c.symm
  let l := folkmanProductEmbeddingLeft p p q.toEmbedding
  let r := folkmanProductEmbeddingRight p p q.toEmbedding
  have hsplit (z) : q z = (l z.1, r z.2) := folkmanProductEmbedding_split p p q.toEmbedding z
  have hl : Function.Surjective l := by
    intro x
    obtain ⟨z, hz⟩ := q.surjective (x, 0)
    exact ⟨z.1, congrArg Prod.fst ((hsplit z).symm.trans hz)⟩
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨z, hz⟩ := q.surjective (0, y)
    exact ⟨z.2, congrArg Prod.snd ((hsplit z).symm.trans hz)⟩
  let el := RingEquiv.ofBijective l ⟨folkmanProductEmbeddingLeft_injective p p q.toEmbedding, hl⟩
  let er := RingEquiv.ofBijective r ⟨folkmanProductEmbeddingRight_injective p p q.toEmbedding, hr⟩
  let ga : folkmanPairedAutomorphisms p :=
    ⟨(el, er), folkmanProductEmbedding_preserves_pairing p p q.toEmbedding⟩
  refine ⟨ga, ?_⟩
  apply Language.Equiv.ext
  intro x
  change c.symm (l (c x).1, r (c x).2) = g.toEquiv x
  rw [← hsplit]
  change c.symm (c (g.toEquiv (c.symm (c x)))) = g.toEquiv x
  simp only [Language.Equiv.symm_apply_apply]

theorem nativePairedToEncoded_continuous (c : letI := folkmanProductStructure p;
    M ≃[folkmanLanguage] (L × R)) :
    Continuous (nativePairedToEncoded p c) := by
  letI := folkmanProductStructure p
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  have heval : Continuous (pairedEvaluation p) := continuous_induced_dom
  have hl : Continuous (fun g : folkmanPairedAutomorphisms p =>
      WithTopology.toTopology (⊥ : TopologicalSpace L) (g.val.1 (c x).1)) :=
    (continuous_apply (c x).1).comp (continuous_fst.comp heval)
  have hr : Continuous (fun g : folkmanPairedAutomorphisms p =>
      WithTopology.toTopology (⊥ : TopologicalSpace R) (g.val.2 (c x).2)) :=
    (continuous_apply (c x).2).comp (continuous_snd.comp heval)
  let combine (z : WithDiscreteTopology L × WithDiscreteTopology R) : WithDiscreteTopology M :=
    WithTopology.toTopology ⊥ (c.symm (WithTopology.ofTopology z.1, WithTopology.ofTopology z.2))
  have hcombine : Continuous combine := continuous_of_discreteTopology
  exact hcombine.comp (hl.prodMk hr)

end General

end SuccessorTree.NonPrecompact
