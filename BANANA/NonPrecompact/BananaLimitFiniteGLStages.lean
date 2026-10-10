import BANANA.NonPrecompact.BananaLimitFiniteGLGroupAction

/-!
# Finite subgroup stages in the automorphism group of the BANANA limit

For each finite rational-coordinate set S, collect the pairs of
globally lifted linear equivalences coming from GL(|S|, F₂).
The collection is finite, contains the identity and is closed under
composition and inverses on both sorts.

The later directed-union step must still verify compatibility of the
stages when S is included in a larger finite coordinate set T.
-/

namespace SuccessorTree.NonPrecompact

/-- A pair of linear automorphisms of the two equal underlying
vector spaces, with the two sorts still distinguished by position. -/
abbrev BananaLimitLinearPair : Type :=
  (BananaLimitVector ≃ₗ[F2] BananaLimitVector) ×
    (BananaLimitVector ≃ₗ[F2] BananaLimitVector)

/-- The finite collection of global automorphism pairs arising from
linear transformations supported in the rational-coordinate block S. -/
def bananaLimitFiniteGLStage (S : Finset ℚ) :
    Set BananaLimitLinearPair :=
  Set.range (bananaLimitFiniteGLAction S)

/-- Each finite-coordinate stage has finitely many automorphism pairs. -/
theorem bananaLimitFiniteGLStage_finite (S : Finset ℚ) :
    Finite {g : BananaLimitLinearPair //
      g ∈ bananaLimitFiniteGLStage S} := by
  classical
  let choose : FinitePerfectGL S.card →
      {g : BananaLimitLinearPair // g ∈ bananaLimitFiniteGLStage S} :=
    fun h => ⟨bananaLimitFiniteGLAction S h, ⟨h, rfl⟩⟩
  apply Finite.of_surjective choose
  intro g
  obtain ⟨h, hh⟩ := g.property
  refine ⟨h, ?_⟩
  apply Subtype.ext
  exact hh

/-- The identity automorphism pair belongs to every finite stage. -/
theorem bananaLimitFiniteGLStage_identity (S : Finset ℚ) :
    (LinearEquiv.refl F2 BananaLimitVector,
      LinearEquiv.refl F2 BananaLimitVector) ∈
      bananaLimitFiniteGLStage S := by
  refine ⟨LinearEquiv.refl F2 (Fin S.card → F2), ?_⟩
  exact Prod.ext (bananaLimitFiniteGLAction_refl S).1
    (bananaLimitFiniteGLAction_refl S).2

/-- A fixed finite stage is closed under simultaneous composition
on the left and right sorts. -/
theorem bananaLimitFiniteGLStage_trans
    (S : Finset ℚ)
    (f g : BananaLimitLinearPair)
    (hf : f ∈ bananaLimitFiniteGLStage S)
    (hg : g ∈ bananaLimitFiniteGLStage S) :
    (f.1.trans g.1, f.2.trans g.2) ∈
      bananaLimitFiniteGLStage S := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  refine ⟨a.trans b, ?_⟩
  exact Prod.ext (bananaLimitFiniteGLAction_trans S a b).1
    (bananaLimitFiniteGLAction_trans S a b).2

/-- The action of the inverse finite GL transformation is the
componentwise inverse global action. -/
theorem bananaLimitFiniteGLAction_symm
    (S : Finset ℚ) (h : FinitePerfectGL S.card) :
    (bananaLimitFiniteGLAction S h.symm).1 =
      (bananaLimitFiniteGLAction S h).1.symm ∧
    (bananaLimitFiniteGLAction S h.symm).2 =
      (bananaLimitFiniteGLAction S h).2.symm := by
  constructor
  · let a := (bananaLimitFiniteGLAction S h).1
    let b := (bananaLimitFiniteGLAction S h.symm).1
    have ht : b.trans a =
        LinearEquiv.refl F2 BananaLimitVector := by
      have htr := (bananaLimitFiniteGLAction_trans S h.symm h).1
      rw [← htr, LinearEquiv.symm_trans_self]
      exact (bananaLimitFiniteGLAction_refl S).1
    apply LinearEquiv.ext
    intro x
    apply a.injective
    calc
      a (b x) = x := by
        have hx := congrArg
          (fun k : BananaLimitVector ≃ₗ[F2] BananaLimitVector => k x) ht
        simpa only [LinearEquiv.trans_apply, LinearEquiv.refl_apply] using hx
      _ = a (a.symm x) := (a.apply_symm_apply x).symm
  · let a := (bananaLimitFiniteGLAction S h).2
    let b := (bananaLimitFiniteGLAction S h.symm).2
    have ht : b.trans a =
        LinearEquiv.refl F2 BananaLimitVector := by
      have htr := (bananaLimitFiniteGLAction_trans S h.symm h).2
      rw [← htr, LinearEquiv.symm_trans_self]
      exact (bananaLimitFiniteGLAction_refl S).2
    apply LinearEquiv.ext
    intro x
    apply a.injective
    calc
      a (b x) = x := by
        have hx := congrArg
          (fun k : BananaLimitVector ≃ₗ[F2] BananaLimitVector => k x) ht
        simpa only [LinearEquiv.trans_apply, LinearEquiv.refl_apply] using hx
      _ = a (a.symm x) := (a.apply_symm_apply x).symm

/-- A fixed finite stage is closed under taking the inverse
automorphism of both sorts. -/
theorem bananaLimitFiniteGLStage_symm
    (S : Finset ℚ) (f : BananaLimitLinearPair)
    (hf : f ∈ bananaLimitFiniteGLStage S) :
    (f.1.symm, f.2.symm) ∈ bananaLimitFiniteGLStage S := by
  obtain ⟨h, rfl⟩ := hf
  refine ⟨h.symm, ?_⟩
  exact Prod.ext (bananaLimitFiniteGLAction_symm S h).1
    (bananaLimitFiniteGLAction_symm S h).2

end SuccessorTree.NonPrecompact
