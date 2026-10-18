import BANANA.NonPrecompact.PrebananaGeneratedProfileEmbedding
import BANANA.NonPrecompact.PrebananaFiveAryCylinderTupleProfile

/-!
# Completing finite profiles to global marked Boolean automorphisms

Equal finite marked profiles of tuples admit a generator-preserving
marked isomorphism between their finite generated Boolean subalgebras.
We transport this isomorphism into the countable cylinder algebra.

The only infinitary input is an explicitly stated hypothesis saying
that two embeddings of the same finite marked Boolean model into the
cylinder algebra are conjugate by a global marking-preserving Boolean
automorphism. That hypothesis is proved independently by finite
back-and-forth; this module does not silently assume homogeneity.

Neither the chosen finite presentations nor their atom enumerations
are assumed canonical. Equality of their profiles suffices.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Under the independently formalised finite-embedding
ultrahomogeneity principle, equal complete marked tuple profiles
are realised by a genuine global marking-preserving Boolean
automorphism carrying the tuples coordinatewise. -/
theorem prebananaCylinder_profile_eq_implies_automorphism
    (hhom :
      ∀ (A : PrebananaFiniteBooleanModel)
        (i j : PrebananaFiniteToCountableEmbedding
          A prebananaCylinderCountableModel),
        ∃ E : PrebananaFiveAryCylinderLimitCarrier ≃o
            PrebananaFiveAryCylinderLimitCarrier,
          (∀ x : PrebananaFiveAryCylinderLimitCarrier,
            prebananaFiveAryCylinderMark (E x) =
              prebananaFiveAryCylinderMark x) ∧
          ∀ a : A.carrier, E (i.hom a) = j.hom a)
    {n : ℕ}
    (xs ys : Fin n → PrebananaFiveAryCylinderLimitCarrier)
    (hprofile :
      prebananaCylinderTupleProfile xs =
        prebananaCylinderTupleProfile ys) :
    ∃ E : PrebananaFiveAryCylinderLimitCarrier ≃o
        PrebananaFiveAryCylinderLimitCarrier,
      (∀ x : PrebananaFiveAryCylinderLimitCarrier,
        prebananaFiveAryCylinderMark (E x) =
          prebananaFiveAryCylinderMark x) ∧
      ∀ i : Fin n, E (xs i) = ys i := by
  classical
  let wx := prebananaCylinderTupleWitness xs
  let wy := prebananaCylinderTupleWitness ys
  change
    prebananaAbstractMarkedTupleProfile
      wx.model.carrier wx.model.μ
      wx.model.μ_bot wx.model.μ_top wx.model.μ_add wx.tuple =
    prebananaAbstractMarkedTupleProfile
      wy.model.carrier wy.model.μ
      wy.model.μ_bot wy.model.μ_top wy.model.μ_add wy.tuple
    at hprofile
  let LX : BooleanSubalgebra wx.model.carrier :=
    prebananaGeneratedBooleanSubalgebra wx.model.carrier wx.tuple
  let LY : BooleanSubalgebra wy.model.carrier :=
    prebananaGeneratedBooleanSubalgebra wy.model.carrier wy.tuple
  let GX : PrebananaFiniteBooleanModel :=
    prebananaFiniteBooleanSubmodel wx.model LX
  let GY : PrebananaFiniteBooleanModel :=
    prebananaFiniteBooleanSubmodel wy.model LY
  let F : PrebananaFiniteBooleanEmbedding GX GY :=
    prebananaFiniteGeneratedMarkedEmbedding_of_profile_eq
      wx.model wy.model wx.tuple wy.tuple hprofile
  let inclX : PrebananaFiniteBooleanEmbedding GX wx.model :=
    prebananaFiniteBooleanSubmodel_embedding wx.model LX
  let inclY : PrebananaFiniteBooleanEmbedding GY wy.model :=
    prebananaFiniteBooleanSubmodel_embedding wy.model LY
  let iX : PrebananaFiniteToCountableEmbedding
      GX prebananaCylinderCountableModel :=
    wx.embedding.comp inclX
  let iY : PrebananaFiniteToCountableEmbedding
      GX prebananaCylinderCountableModel :=
    (wy.embedding.comp inclY).comp F
  obtain ⟨E, hmark, hemb⟩ := hhom GX iX iY
  refine ⟨E, hmark, ?_⟩
  intro i
  let a : GX.carrier :=
    ⟨wx.tuple i,
      BooleanSubalgebra.subset_closure (Set.mem_range_self i)⟩
  have hleft : iX.hom a = xs i := by
    exact wx.covers i
  have hright : iY.hom a = ys i := by
    have hmap : (F.hom a).val = wy.tuple i :=
      prebananaFiniteGeneratedMarkedEmbedding_map_generator
        wx.model wy.model wx.tuple wy.tuple hprofile i
    change wy.embedding.hom (F.hom a).val = ys i
    rw [hmap]
    exact wy.covers i
  calc
    E (xs i) = E (iX.hom a) := congrArg E hleft.symm
    _ = iY.hom a := hemb a
    _ = ys i := hright

end SuccessorTree.NonPrecompact
