import BANANA.NonPrecompact.BananaLimitUniversality
import Mathlib.Data.Fintype.EquivFin

/-!
# Cofinality of perfect finite blocks in the explicit BANANA limit

Every finite family of vectors, on both sorts, is contained in a
single finite rational-coordinate block. That *particular* block is
canonically isomorphic (after a finite enumeration of its coordinates)
to a standard perfect BANANA pairing.

This strengthens mere existence of finite perfect blocks: the chosen
block can contain any prescribed finite families simultaneously.
It gives the finite-substructure side of the age calculation, leaving
ultrahomogeneity and ω-categoricity as separate obligations.
-/

namespace SuccessorTree.NonPrecompact

/-- A prescribed finite block is isomorphic to the standard binary
coordinate space of dimension equal to the number of its indices. -/
noncomputable def bananaLimitBlockStandardEquiv (S : Finset ℚ) :
    (Fin S.card → F2) ≃ₗ[F2] bananaLimitBlock S := by
  classical
  let e : (S : Type) ≃ Fin S.card :=
    Fintype.equivFinOfCardEq (by simp)
  exact (LinearEquiv.funCongrLeft F2 F2 e).trans
    (bananaLimitBlockEquiv S).symm

/-- The fixed block equivalence identifies the restricted ambient
pairing with the standard perfect dot product. -/
theorem bananaLimitBlockStandardEquiv_pairing
    (S : Finset ℚ) (x y : Fin S.card → F2) :
    bananaLimitPairing
      (bananaLimitBlockStandardEquiv S x)
      (bananaLimitBlockStandardEquiv S y) = x ⬝ᵥ y := by
  classical
  rw [bananaLimitBlock_pairing_eq_dotProduct]
  let e : (S : Type) ≃ Fin S.card :=
    Fintype.equivFinOfCardEq (by simp)
  simp only [bananaLimitBlockStandardEquiv,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  change (fun q : S => x (e q)) ⬝ᵥ
      (fun q : S => y (e q)) = x ⬝ᵥ y
  simp only [dotProduct]
  simpa only [Equiv.apply_symm_apply] using
    (Equiv.sum_comp e.symm
      (fun q : S => x (e q) * y (e q))).symm

/-- The canonical embedding of the standard perfect pairing into
the *specified* finite rational-coordinate block. -/
noncomputable def bananaLimitBlockStandardEmbedding
    (S : Finset ℚ) :
    BananaMatrixEmbeddingToLimit (perfectBanana S.card) := by
  classical
  let E := bananaLimitBlockStandardEquiv S
  let f : (Fin S.card → F2) →ₗ[F2] BananaLimitVector :=
    (bananaLimitBlock S).subtype.comp E.toLinearMap
  refine {
    left := f
    right := f
    left_injective :=
      (bananaLimitBlock S).injective_subtype.comp E.injective
    right_injective :=
      (bananaLimitBlock S).injective_subtype.comp E.injective
    pairing_apply := ?_
  }
  intro x y
  change bananaLimitPairing (E x : BananaLimitVector)
    (E y : BananaLimitVector) = (perfectBanana S.card).eval x y
  simpa only [perfectBanana_eval] using
    (bananaLimitBlockStandardEquiv_pairing S x y)

/-- Every vector supported inside a given finite block is the image
of some standard coordinate vector under the canonical embedding. -/
theorem bananaLimitBlockStandardEmbedding_surjective_on_block
    (S : Finset ℚ) (v : BananaLimitVector)
    (hv : v ∈ bananaLimitBlock S) :
    ∃ x : Fin S.card → F2,
      (bananaLimitBlockStandardEmbedding S).left x = v := by
  classical
  let u : bananaLimitBlock S := ⟨v, hv⟩
  let E := bananaLimitBlockStandardEquiv S
  refine ⟨E.symm u, ?_⟩
  change ((E (E.symm u) : bananaLimitBlock S) : BananaLimitVector) = v
  exact congrArg Subtype.val (E.apply_symm_apply u)

/-- An arbitrary finite family of vectors on both sorts is contained
in the image of a *single* standard perfect pairing. -/
theorem exists_perfect_block_containing_finite_families
    (left right : Finset BananaLimitVector) :
    ∃ n : ℕ,
    ∃ e : BananaMatrixEmbeddingToLimit (perfectBanana n),
      (∀ v ∈ left, ∃ x : Fin n → F2, e.left x = v) ∧
      (∀ w ∈ right, ∃ y : Fin n → F2, e.right y = w) := by
  classical
  let S := bananaLimitCommonSupport left right
  refine ⟨S.card, bananaLimitBlockStandardEmbedding S, ?_, ?_⟩
  · intro v hv
    exact bananaLimitBlockStandardEmbedding_surjective_on_block
      S v (bananaLimit_left_mem_common_block left right v hv)
  · intro w hw
    exact bananaLimitBlockStandardEmbedding_surjective_on_block
      S w (bananaLimit_right_mem_common_block left right w hw)

/-- The same cofinality assertion for any two finite-dimensional
subspaces which have finite underlying sets (as over F₂). -/
theorem exists_perfect_block_containing_finite_subspaces
    (U V : Submodule F2 BananaLimitVector)
    [Finite U] [Finite V] :
    ∃ n : ℕ,
    ∃ e : BananaMatrixEmbeddingToLimit (perfectBanana n),
      (∀ v : U, ∃ x : Fin n → F2, e.left x = (v : BananaLimitVector)) ∧
      (∀ w : V, ∃ y : Fin n → F2, e.right y = (w : BananaLimitVector)) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  letI : Fintype V := Fintype.ofFinite V
  let left : Finset BananaLimitVector :=
    (Finset.univ : Finset U).image (fun v : U => (v : BananaLimitVector))
  let right : Finset BananaLimitVector :=
    (Finset.univ : Finset V).image (fun v : V => (v : BananaLimitVector))
  obtain ⟨n, e, hleft, hright⟩ :=
    exists_perfect_block_containing_finite_families left right
  refine ⟨n, e, ?_, ?_⟩
  · intro v
    apply hleft v
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  · intro w
    apply hright w
    exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩

end SuccessorTree.NonPrecompact
