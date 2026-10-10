import BANANA.NonPrecompact.BananaLimitFiniteGLStageInclusions
import BANANA.NonPrecompact.BananaLimitFiniteGLStages

/-!
# The directed union of finite GL automorphism stages

The stages of finite rational-coordinate support are finite and
closed under identity, composition and inversion. Their inclusions
for nested supports make the union a subgroup in the algebraic sense.

Every finite family in this union lies in one finite stage, which
is the precise local-finiteness property. No topological amenability
statement is made here.
-/

namespace SuccessorTree.NonPrecompact

/-- Monotonicity of the finite automorphism stages for nested
rational coordinate sets. -/
theorem bananaLimitFiniteGLStage_mono
    (S T : Finset ℚ) (hST : S ⊆ T) :
    bananaLimitFiniteGLStage S ⊆ bananaLimitFiniteGLStage T := by
  intro g hg
  obtain ⟨h, rfl⟩ := hg
  obtain ⟨k, hL, hR⟩ :=
    exists_bananaLimitFiniteGLAction_larger_stage S T hST h
  exact ⟨k, Prod.ext hL hR⟩

/-- Any two stages lie in the single finite stage indexed by
the union of their supports. -/
theorem bananaLimitFiniteGLStage_directed
    (S T : Finset ℚ) :
    bananaLimitFiniteGLStage S ⊆ bananaLimitFiniteGLStage (S ∪ T) ∧
    bananaLimitFiniteGLStage T ⊆ bananaLimitFiniteGLStage (S ∪ T) :=
  ⟨bananaLimitFiniteGLStage_mono S (S ∪ T) Finset.subset_union_left,
   bananaLimitFiniteGLStage_mono T (S ∪ T) Finset.subset_union_right⟩

/-- The union of finite automorphism stages over all finite supports. -/
def bananaLimitFiniteGLUnion : Set BananaLimitLinearPair :=
  {g | ∃ S : Finset ℚ, g ∈ bananaLimitFiniteGLStage S}

/-- The identity automorphism belongs to the directed union. -/
theorem bananaLimitFiniteGLUnion_identity :
    (LinearEquiv.refl F2 BananaLimitVector,
      LinearEquiv.refl F2 BananaLimitVector) ∈
      bananaLimitFiniteGLUnion := by
  exact ⟨∅, bananaLimitFiniteGLStage_identity ∅⟩

/-- The directed union is closed under simultaneous composition. -/
theorem bananaLimitFiniteGLUnion_trans
    (f g : BananaLimitLinearPair)
    (hf : f ∈ bananaLimitFiniteGLUnion)
    (hg : g ∈ bananaLimitFiniteGLUnion) :
    (f.1.trans g.1, f.2.trans g.2) ∈
      bananaLimitFiniteGLUnion := by
  obtain ⟨S, hfS⟩ := hf
  obtain ⟨T, hgT⟩ := hg
  refine ⟨S ∪ T, ?_⟩
  apply bananaLimitFiniteGLStage_trans
  · exact bananaLimitFiniteGLStage_mono S (S ∪ T)
      Finset.subset_union_left hfS
  · exact bananaLimitFiniteGLStage_mono T (S ∪ T)
      Finset.subset_union_right hgT

/-- The directed union is closed under componentwise inversion. -/
theorem bananaLimitFiniteGLUnion_symm
    (f : BananaLimitLinearPair)
    (hf : f ∈ bananaLimitFiniteGLUnion) :
    (f.1.symm, f.2.symm) ∈ bananaLimitFiniteGLUnion := by
  obtain ⟨S, hfS⟩ := hf
  exact ⟨S, bananaLimitFiniteGLStage_symm S f hfS⟩

/-- Every finite family of global automorphisms from the union
lies in a common finite stage. -/
theorem bananaLimitFiniteGLUnion_finite_family_common_stage
    (xs : Finset BananaLimitLinearPair)
    (hxs : ∀ g ∈ xs, g ∈ bananaLimitFiniteGLUnion) :
    ∃ S : Finset ℚ, ∀ g ∈ xs, g ∈ bananaLimitFiniteGLStage S := by
  classical
  induction xs using Finset.induction_on with
  | empty =>
      refine ⟨∅, ?_⟩
      intro g hg
      simp at hg
  | @insert a xs ha ih =>
      obtain ⟨S, haS⟩ := hxs a (Finset.mem_insert_self a xs)
      obtain ⟨T, hT⟩ := ih (by
        intro g hg
        exact hxs g (Finset.mem_insert_of_mem hg))
      refine ⟨S ∪ T, ?_⟩
      intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hmem
      · exact bananaLimitFiniteGLStage_mono S (S ∪ T)
          Finset.subset_union_left haS
      · exact bananaLimitFiniteGLStage_mono T (S ∪ T)
          Finset.subset_union_right (hT g hmem)

/-- Each global action in the union preserves the two-sorted pairing. -/
theorem bananaLimitFiniteGLUnion_pairing
    (f : BananaLimitLinearPair) (hf : f ∈ bananaLimitFiniteGLUnion)
    (x y : BananaLimitVector) :
    bananaLimitPairing (f.1 x) (f.2 y) =
      bananaLimitPairing x y := by
  obtain ⟨S, h, rfl⟩ := hf
  exact bananaLimitFiniteGLAction_pairing S h x y

end SuccessorTree.NonPrecompact
