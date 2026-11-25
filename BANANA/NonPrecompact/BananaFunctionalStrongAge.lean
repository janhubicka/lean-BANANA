import BANANA.NonPrecompact.BananaFunctionalLimit
import BANANA.NonPrecompact.BananaNativeStrongAmalgamation
import BANANA.NonPrecompact.FirstOrderFunctionalRamseyAge

/-!
# Strong amalgamation in the functional first-order BANANA age
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder CategoryTheory
open scoped FirstOrder

namespace BananaFunctional

/-- Any native finite-dimensional bilinear pairing embeds into the explicit
functional BANANA limit. -/
theorem native_mem_age {L R : Type} [AddCommGroup L] [AddCommGroup R]
    [Module F2 L] [Module F2 R] [Module.Finite F2 L] [Module.Finite F2 R]
    (β : L →ₗ[F2] R →ₗ[F2] F2) :
    (⟨L ⊕ R, structureOn (fun x y => β x y)⟩ : Bundled bananaFunctionalLanguage.Structure)
      ∈ bananaFunctionalLanguage.age BananaTaggedCarrier := by
  let := structureOn (fun x y => β x y)
  let bL := Module.finBasis F2 L
  let bR := Module.finBasis F2 R
  let _ : Finite L := Finite.of_injective bL.equivFun bL.equivFun.injective
  let _ : Finite R := Finite.of_injective bR.equivFun bR.equivFun.injective
  let A := BananaNative.coordinates β bL bR
  obtain ⟨f⟩ := A.embeds_in_explicit_limit
  refine ⟨Language.Structure.FG.of_finite, ⟨embedding _ bananaLimitPairing
    (f.left.comp bL.equivFun.toLinearMap) (f.right.comp bR.equivFun.toLinearMap)
    (f.left_injective.comp bL.equivFun.injective) (f.right_injective.comp bR.equivFun.injective)
    (fun x y => (f.pairing_apply (bL.equivFun x) (bR.equivFun y)).trans
      (BananaNative.coordinates_eval β bL bR x y))⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Native strong amalgamation lifts through the presentation because its
embeddings preserve each sort and are exactly native linear embeddings. -/
theorem strong_age : FirstOrderStrongAmalgamation
    (bananaFunctionalLanguage.age BananaTaggedCarrier) := by
  intro A B C f g hA hB hC
  let a := hA.2.some
  let b := hB.2.some
  let c := hC.2.some
  let SA := a.toHom.range
  let SB := b.toHom.range
  let SC := c.toHom.range
  let PA := restrictBilinear SA
  let PB := restrictBilinear SB
  let PC := restrictBilinear SC
  let α := restrictedPairing bananaLimitPairing SA
  let β := restrictedPairing bananaLimitPairing SB
  let γ := restrictedPairing bananaLimitPairing SC
  let := structureOn α
  let := structureOn β
  let := structureOn γ
  let ea := ageMemberEquiv A a
  let eb := ageMemberEquiv B b
  let ec := ageMemberEquiv C c
  let P := (eb.toEmbedding.comp f).comp ea.symm.toEmbedding
  let Q := (ec.toEmbedding.comp g).comp ea.symm.toEmbedding
  let p : BananaNative.PairingEmbedding (fun x y => PA x y) (fun x y => PB x y) :=
    ⟨leftLinear α β P, rightLinear α β P,
      leftLinear_injective α β P, rightLinear_injective α β P, fun x y => by
        simpa only [PA, PB, restrictBilinear_apply] using map_pairing α β P x y⟩
  let q : BananaNative.PairingEmbedding (fun x y => PA x y) (fun x y => PC x y) :=
    ⟨leftLinear α γ Q, rightLinear α γ Q,
      leftLinear_injective α γ Q, rightLinear_injective α γ Q, fun x y => by
        simpa only [PA, PC, restrictBilinear_apply] using map_pairing α γ Q x y⟩
  let _ : Finite SA := finite_of_fg SA (hA.1.range a.toHom)
  let _ : Finite SB := finite_of_fg SB (hB.1.range b.toHom)
  let _ : Finite SC := finite_of_fg SC (hC.1.range c.toHom)
  let _ := finite_leftSubspace bananaLimitPairing SA
  let _ := finite_rightSubspace bananaLimitPairing SA
  let _ := finite_leftSubspace bananaLimitPairing SB
  let _ := finite_rightSubspace bananaLimitPairing SB
  let _ := finite_leftSubspace bananaLimitPairing SC
  let _ := finite_rightSubspace bananaLimitPairing SC
  have amalgam := BananaNative.exists_finiteStrongAmalgam
    (A₁ := leftSubspace bananaLimitPairing SA) (A₂ := rightSubspace bananaLimitPairing SA)
    (B₁ := leftSubspace bananaLimitPairing SB) (B₂ := rightSubspace bananaLimitPairing SB)
    (C₁ := leftSubspace bananaLimitPairing SC) (C₂ := rightSubspace bananaLimitPairing SC)
    PA PB PC p q
  obtain ⟨DL, DR, hDL, hDR, mDL, mDR, fDL, fDR, δ, F, G, h⟩ := amalgam
  let _ := hDL
  let _ := hDR
  let _ := mDL
  let _ := mDR
  let _ := fDL
  let _ := fDR
  let D : Bundled bananaFunctionalLanguage.Structure :=
    ⟨DL ⊕ DR, structureOn (fun x y => δ x y)⟩
  let := D.str
  let jf := embedding β (fun x y => δ x y) F.left F.right
    F.left_injective F.right_injective (fun x y => by
      simpa only [PB, restrictBilinear_apply] using F.preserves x y)
  let jg := embedding γ (fun x y => δ x y) G.left G.right
    G.left_injective G.right_injective (fun x y => by
      simpa only [PC, restrictBilinear_apply] using G.preserves x y)
  have hD : D ∈ bananaFunctionalLanguage.age BananaTaggedCarrier := native_mem_age δ
  have hP x : eb (f x) = P (ea x) := by simp [P]
  have hQ x : ec (g x) = Q (ea x) := by simp [Q]
  refine ⟨D, jf.comp eb.toEmbedding, jg.comp ec.toEmbedding, hD, ?_, ?_⟩
  · apply Language.Embedding.ext
    intro z
    change jf (eb (f z)) = jg (ec (g z))
    rw [hP, hQ]
    cases hz : ea z with
    | inl x =>
      rw [map_inl_linear α β P, map_inl_linear α γ Q]
      exact congrArg Sum.inl (LinearMap.congr_fun h.comm_left x)
    | inr y =>
      rw [map_inr_linear α β P, map_inr_linear α γ Q]
      exact congrArg Sum.inr (LinearMap.congr_fun h.comm_right y)
  · intro y x hxy
    have heq : jf (eb x) = jg (ec y) := hxy.symm
    cases hx : eb x <;> cases hy : ec y <;> rw [hx, hy] at heq
    · rename_i u v
      obtain ⟨z, _, hz⟩ := (h.intersection_left u v).mp (Sum.inl.inj heq)
      refine ⟨ea.symm (.inl z), ec.injective ?_⟩
      rw [hQ, ea.apply_symm_apply, map_inl_linear α γ Q, hy, hz]
    · rename_i u v
      change (Sum.inl (F.left u) : DL ⊕ DR) = Sum.inr (G.right v) at heq
      cases heq
    · rename_i u v
      change (Sum.inr (F.right u) : DL ⊕ DR) = Sum.inl (G.left v) at heq
      cases heq
    · rename_i u v
      obtain ⟨z, _, hz⟩ := (h.intersection_right u v).mp (Sum.inr.inj heq)
      refine ⟨ea.symm (.inr z), ec.injective ?_⟩
      rw [hQ, ea.apply_symm_apply, map_inr_linear α γ Q, hy, hz]

/-- The countably infinite functional BANANA age also has a reasonable
precompact Ramsey expansion by added functions and named point predicates. -/
theorem exists_namedFunctionalRamseyAge :
    ∃ F : FiniteClosureFamily bananaFunctionalLanguage BananaTaggedCarrier,
      IsReasonablePrecompactRamseyAge F := by
  classical
  let single (q : ℚ) : BananaTaggedCarrier := Sum.inl (Finsupp.single q (1 : F2))
  let _ := Infinite.of_injective single
    (Sum.inl_injective.comp (Finsupp.single_left_injective one_ne_zero))
  apply firstOrder_exists_namedFunctionalRamseyAge_of_oligomorphic finite_of_fg
    limit_ultrahomogeneous strong_age
  intro n
  obtain ⟨R, hR⟩ := finite_tuple_orbit_representatives n
  let mk : (Fin n → BananaTaggedCarrier) → Quotient (firstOrderTupleOrbit
    bananaFunctionalLanguage BananaTaggedCarrier n) := Quotient.mk _
  apply Finite.of_surjective (fun r : R => mk r)
  intro q
  obtain ⟨r, hr, g, hg⟩ := hR q.out
  refine ⟨⟨r, hr⟩, ?_⟩
  have h : (firstOrderTupleOrbit bananaFunctionalLanguage BananaTaggedCarrier n).r r q.out :=
    ⟨g.toEquiv, congrFun hg⟩
  exact (Quotient.sound h).trans (Quotient.out_eq q)

end BananaFunctional
end SuccessorTree.NonPrecompact
