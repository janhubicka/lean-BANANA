import BANANA.NonPrecompact.BananaLimitBilinearity
import BANANA.NonPrecompact.WittCountable

/-!
# The countable orthogonal sum of binary hyperbolic planes

Two finitely supported binary vectors record the two coordinates in each
hyperbolic plane. The formula uses the dot product already defined for the
two-sorted BANANA model and gives a one-sorted alternating space.
-/

namespace SuccessorTree.NonPrecompact

/-- The two coordinates per hyperbolic plane are indexed by a countably
infinite set, using the existing finitely supported coordinate space. -/
abbrev CountableSymplectic := BananaLimitVector × BananaLimitVector

/-- The form of the orthogonal sum, with the two cross terms in each plane. -/
noncomputable def countableSymplecticForm : LinearMap.BilinForm F2 CountableSymplectic where
  toFun x := (bananaLimitPairingRightLinear x.1).comp (LinearMap.snd _ _ _) -
    (bananaLimitPairingLeftLinear x.2).comp (LinearMap.fst _ _ _)
  map_add' x y := by
    refine LinearMap.ext (fun z => ?_)
    change bananaLimitPairing (x.1 + y.1) z.2 - bananaLimitPairing z.1 (x.2 + y.2) =
      (bananaLimitPairing x.1 z.2 - bananaLimitPairing z.1 x.2) +
      (bananaLimitPairing y.1 z.2 - bananaLimitPairing z.1 y.2)
    rw [bananaLimitPairing_add_left, bananaLimitPairing_add_right]
    exact (sub_add_sub_comm _ _ _ _).symm
  map_smul' c x := by
    refine LinearMap.ext (fun z => ?_)
    change bananaLimitPairing (c • x.1) z.2 - bananaLimitPairing z.1 (c • x.2) =
      c * (bananaLimitPairing x.1 z.2 - bananaLimitPairing z.1 x.2)
    rw [bananaLimitPairing_smul_left, bananaLimitPairing_smul_right, mul_sub]

theorem countableSymplecticForm_apply (x y : CountableSymplectic) :
    countableSymplecticForm x y =
      bananaLimitPairing x.1 y.2 - bananaLimitPairing y.1 x.2 := rfl

theorem countableSymplecticForm_isAlt : countableSymplecticForm.IsAlt := by
  intro x
  rw [countableSymplecticForm_apply, sub_self]

/-- The two coordinates at each index pair to one, and coordinates from
distinct indices are orthogonal. The same-coordinate blocks both vanish. -/
theorem countableSymplecticForm_coordinate_pairings (i j : ℚ) :
    countableSymplecticForm (Finsupp.single i 1, 0) (0, Finsupp.single j 1) =
      (if i = j then 1 else 0) ∧
    countableSymplecticForm (Finsupp.single i 1, 0) (Finsupp.single j 1, 0) = 0 ∧
    countableSymplecticForm (0, Finsupp.single i 1) (0, Finsupp.single j 1) = 0 := by
  simp [countableSymplecticForm_apply, bananaLimitPairing_single,
    bananaLimitPairing_zero_left, bananaLimitPairing_zero_right]

private theorem dot_single_right (u : BananaLimitVector) (i : ℚ) :
    bananaLimitPairing u (Finsupp.single i 1) = u i := by
  classical
  change (∑ j ∈ u.support, u j * (Finsupp.single i (1 : F2)) j) = u i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji.symm]
  · intro hi
    simp [Finsupp.notMem_support_iff.mp hi]

private theorem dot_single_left (u : BananaLimitVector) (i : ℚ) :
    bananaLimitPairing (Finsupp.single i 1) u = u i := by
  classical
  simp [bananaLimitPairing]

theorem countableSymplecticForm_nondegenerate : countableSymplecticForm.Nondegenerate := by
  have hleft : countableSymplecticForm.SeparatingLeft := by
    intro x hx
    apply Prod.ext <;> ext i
    · simpa [countableSymplecticForm_apply, dot_single_right,
        bananaLimitPairing_zero_left] using hx (0, Finsupp.single i 1)
    · simpa [countableSymplecticForm_apply, dot_single_left,
        bananaLimitPairing_zero_right] using hx (Finsupp.single i 1, 0)
  refine ⟨hleft, fun x hx => hleft x (fun y => ?_)⟩
  rw [← neg_eq_zero, countableSymplecticForm_isAlt.neg_eq, hx]

theorem countableSymplectic_not_finiteDimensional :
    ¬ FiniteDimensional F2 CountableSymplectic := by
  intro h
  let _ : FiniteDimensional F2 CountableSymplectic := h
  have hfinite : Module.Finite F2 (ℚ →₀ F2) :=
    FiniteDimensional.of_surjective (LinearMap.fst F2 BananaLimitVector BananaLimitVector)
      (fun u => ⟨(u, 0), rfl⟩)
  rcases Module.finite_finsupp_self_iff.mp hfinite with hF2 | hQ
  · exact not_subsingleton F2 hF2
  · let _ : Finite ℚ := hQ
    exact not_finite ℚ

/-- Every partial isometry with finite-dimensional domain in the concrete
countable symplectic space extends to a global isometric automorphism. -/
theorem exists_countableSymplectic_automorphism
    (S : Submodule F2 CountableSymplectic) [FiniteDimensional F2 S]
    (f : S →ₗ[F2] CountableSymplectic) (hf : Function.Injective f)
    (hiso : ∀ u v : S, countableSymplecticForm (f u) (f v) = countableSymplecticForm u v) :
    ∃ g : CountableSymplectic ≃ₗ[F2] CountableSymplectic,
      (∀ u v, countableSymplecticForm (g u) (g v) = countableSymplecticForm u v) ∧
      ∀ u : S, g u = f u :=
  exists_wittCountableIsometry countableSymplecticForm countableSymplecticForm_isAlt
    countableSymplecticForm_nondegenerate countableSymplectic_not_finiteDimensional S f hf hiso

/-- The finite age of the concrete space consists of all finite-dimensional
alternating forms over F₂, including the degenerate ones. -/
theorem countableSymplectic_finite_age {V : Type*} [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] (B : LinearMap.BilinForm F2 V) :
    B.IsAlt ↔ ∃ f : V →ₗ[F2] CountableSymplectic, Function.Injective f ∧
      ∀ u v, countableSymplecticForm (f u) (f v) = B u v := by
  refine ⟨fun hB => ?_, ?_⟩
  · have extend (S : Submodule F2 V) (hS : S.FG) :
        ∃ f : S →ₗ[F2] CountableSymplectic, Function.Injective f ∧
          ∀ u v : S, countableSymplecticForm (f u) (f v) = B u v := by
      induction S, hS using Submodule.fg_sup_span_induction with
      | bot =>
        refine ⟨0, fun u v _ => Subsingleton.elim u v, fun u v => ?_⟩
        have hu : (u : V) = 0 := u.property
        simp [hu]
      | sup S x hS ih =>
        obtain ⟨f, hf, hiso⟩ := ih
        by_cases hx : x ∈ S
        · have hs : F2 ∙ x ≤ S := (Submodule.span_singleton_le_iff_mem x S).mpr hx
          have hST : S ⊔ F2 ∙ x ≤ S := sup_le le_rfl hs
          let i := Submodule.inclusion hST
          exact ⟨f.comp i, hf.comp (Submodule.inclusion_injective hST), fun u v => hiso (i u) (i v)⟩
        · obtain ⟨g, hg, hiso', _⟩ := exists_wittOnePointIsometry B countableSymplecticForm hB
            countableSymplecticForm_isAlt countableSymplecticForm_nondegenerate
            countableSymplectic_not_finiteDimensional S f hf hiso x hx
          exact ⟨g, hg, hiso'⟩
    obtain ⟨f, hf, hpres⟩ := extend ⊤ (Module.Finite.fg_top)
    let e := (Submodule.topEquiv : (⊤ : Submodule F2 V) ≃ₗ[F2] V).symm
    exact ⟨f.comp e.toLinearMap, hf.comp e.injective, fun u v => hpres (e u) (e v)⟩
  · rintro ⟨f, _, hf⟩ x
    rw [← hf]
    exact countableSymplecticForm_isAlt.self_eq_zero (f x)

end SuccessorTree.NonPrecompact
