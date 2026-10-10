import BANANA.NonPrecompact.BananaLimitBlockExtendRestriction
import BANANA.NonPrecompact.BananaLimitFiniteGLAction
import BANANA.NonPrecompact.PerfectHomogeneity

/-!
# Inclusion of finite GL automorphism stages on the BANANA limit

If finite rational supports satisfy S⊆T, every global
contragredient automorphism supported on S is exactly an element of
the finite GL stage supported on T. The parameter on T is obtained
by restricting the two global maps to T, conjugating through the
standard perfect-coordinate identification, and using nondegeneracy
of the T pairing to recover the right map as the contragredient.

This is the directedness ingredient in the locally finite dense
subgroup of the automorphism group in the circulation manuscript.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- Every global finite-GL action supported on S is also a global
finite-GL action at any larger coordinate set T⊇S. Both sorts
agree as linear equivalences on the *entire* countable limit. -/
theorem exists_bananaLimitFiniteGLAction_larger_stage
    (S T : Finset ℚ) (hST : S ⊆ T)
    (h : FinitePerfectGL S.card) :
    ∃ k : FinitePerfectGL T.card,
      (bananaLimitFiniteGLAction T k).1 =
        (bananaLimitFiniteGLAction S h).1 ∧
      (bananaLimitFiniteGLAction T k).2 =
        (bananaLimitFiniteGLAction S h).2 := by
  classical
  let E := bananaLimitBlockStandardEquiv T
  let L : bananaLimitBlock T ≃ₗ[F2] bananaLimitBlock T :=
    bananaLimitBlockLiftRestrict S T hST
      (bananaLimitFiniteGLBlockLeft S h)
  let R : bananaLimitBlock T ≃ₗ[F2] bananaLimitBlock T :=
    bananaLimitBlockLiftRestrict S T hST
      (bananaLimitFiniteGLBlockRight S h)
  let k : FinitePerfectGL T.card :=
    (E.trans L).trans E.symm
  let r : FinitePerfectGL T.card :=
    (E.trans R).trans E.symm
  have hpairT (x y : Fin T.card → F2) :
      k x ⬝ᵥ r y = x ⬝ᵥ y := by
    have hp :=
      bananaLimitBlockLiftRestrict_pairing S T hST
        (bananaLimitFiniteGLBlockLeft S h)
        (bananaLimitFiniteGLBlockRight S h)
        (bananaLimitFiniteGLBlock_pairing S h) (E x) (E y)
    change bananaLimitPairing (L (E x) : BananaLimitVector)
      (R (E y) : BananaLimitVector) =
        bananaLimitPairing (E x : BananaLimitVector)
          (E y : BananaLimitVector) at hp
    calc
      k x ⬝ᵥ r y =
          bananaLimitPairing (E (k x) : BananaLimitVector)
            (E (r y) : BananaLimitVector) :=
          (bananaLimitBlockStandardEquiv_pairing T _ _).symm
      _ = bananaLimitPairing (L (E x) : BananaLimitVector)
            (R (E y) : BananaLimitVector) := by
          simp only [k, r, LinearEquiv.trans_apply,
            LinearEquiv.symm_apply_apply,
            LinearEquiv.apply_symm_apply]
      _ = bananaLimitPairing (E x : BananaLimitVector)
            (E y : BananaLimitVector) := hp
      _ = x ⬝ᵥ y := bananaLimitBlockStandardEquiv_pairing T x y
  have hr : r = dotContragredient k := by
    apply LinearEquiv.ext
    intro y
    apply dotProduct_eq
    intro z
    obtain ⟨x, rfl⟩ := k.surjective z
    calc
      r y ⬝ᵥ k x = k x ⬝ᵥ r y := by rw [dotProduct_comm]
      _ = x ⬝ᵥ y := hpairT x y
      _ = k x ⬝ᵥ dotContragredient k y :=
        (dotContragredient_pairing k x y).symm
      _ = dotContragredient k y ⬝ᵥ k x := by
        rw [dotProduct_comm]
  have hkL : bananaLimitFiniteGLBlockLeft T k = L := by
    apply LinearEquiv.ext
    intro u
    change E (k (E.symm u)) = L u
    simp only [k, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  have hkR : bananaLimitFiniteGLBlockRight T k = R := by
    apply LinearEquiv.ext
    intro u
    change E (dotContragredient k (E.symm u)) = R u
    rw [← hr]
    simp only [r, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  refine ⟨k, ?_, ?_⟩
  · change bananaLimitBlockLift T (bananaLimitFiniteGLBlockLeft T k) =
      bananaLimitBlockLift S (bananaLimitFiniteGLBlockLeft S h)
    rw [hkL]
    exact bananaLimitBlockLift_extend_restriction S T hST
      (bananaLimitFiniteGLBlockLeft S h)
  · change bananaLimitBlockLift T (bananaLimitFiniteGLBlockRight T k) =
      bananaLimitBlockLift S (bananaLimitFiniteGLBlockRight S h)
    rw [hkR]
    exact bananaLimitBlockLift_extend_restriction S T hST
      (bananaLimitFiniteGLBlockRight S h)

end SuccessorTree.NonPrecompact
