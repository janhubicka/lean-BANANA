import BANANA.NonPrecompact.BananaLimitFirstOrderAutomorphism
import BANANA.NonPrecompact.BananaLimitParameterColouring
import BANANA.NonPrecompact.BananaLimitLocalFiniteness
import BANANA.NonPrecompact.FirstOrderDefinableTupleRamsey

/-!
# Definable finite tuple colourings in the tagged BANANA limit

The zero-cross-pairing argument gives a copy of the target block
on which the parameter stabiliser is transitive on each family of
embeddings of the source. Elementary equivalence of tuples gives
the suitable source embeddings through the tuple-automorphism
criterion. The definable colours are truth values of formulas
with the indicated finite parameter tuple.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

private def leftVector : BananaTaggedCarrier → BananaLimitVector :=
  Sum.elim id (fun _ => 0)

private def rightVector : BananaTaggedCarrier → BananaLimitVector :=
  Sum.elim (fun _ => 0) id

private theorem leftVector_smul (g : BananaLimitAutomorphism) (x : BananaTaggedCarrier) :
    leftVector (g • x) = g.val.1 (leftVector x) := by
  cases x with
  | inl x => rfl
  | inr y => exact g.val.1.map_zero.symm

private theorem rightVector_smul (g : BananaLimitAutomorphism) (x : BananaTaggedCarrier) :
    rightVector (g • x) = g.val.2 (rightVector x) := by
  cases x with
  | inl x => exact g.val.2.map_zero.symm
  | inr y => rfl

private theorem native_formula_realize {l k : ℕ} (g : BananaLimitAutomorphism)
    (a : Fin l → BananaTaggedCarrier) (p : Fin k → BananaTaggedCarrier)
    (hp : ∀ i, g • p i = p i)
    (φ : bananaTaggedLanguage.Formula (Fin l ⊕ Fin k)) :
    φ.Realize (Sum.elim (g • a) p) ↔ φ.Realize (Sum.elim a p) := by
  have h : ((bananaLimit_firstOrderAut g).toEquiv : BananaTaggedCarrier → BananaTaggedCarrier) ∘
      Sum.elim a p = Sum.elim (g • a) p := by
    funext i
    cases i with
    | inl j => exact bananaLimit_firstOrderAut_apply g (a j)
    | inr j => exact (bananaLimit_firstOrderAut_apply g (p j)).trans (hp j)
  rw [← h]
  exact Language.StrongHomClass.realize_formula (bananaLimit_firstOrderAut g).toEquiv φ

/-- For native orbit-equivalent subtuples, every finite formula
colouring with parameters has a monochromatic target tuple in
the orbit of the original target. -/
theorem bananaLimit_definableColouring_on_tupleOrbits
    {l r k colours : ℕ} (a : Fin l → BananaTaggedCarrier)
    (b : Fin r → BananaTaggedCarrier) (p : Fin k → BananaTaggedCarrier)
    (φ : Fin colours → bananaTaggedLanguage.Formula (Fin l ⊕ Fin k)) :
    ∃ b' : Fin r → BananaTaggedCarrier,
      SameFormulaType (L := bananaTaggedLanguage) b b' ∧
      ∀ i j : Fin l → Fin r,
        (∃ h : BananaLimitAutomorphism, h • a = b ∘ i) →
        (∃ h : BananaLimitAutomorphism, h • a = b ∘ j) →
        ∀ c, (φ c).Realize (Sum.elim (b' ∘ i) p) ↔
          (φ c).Realize (Sum.elim (b' ∘ j) p) := by
  classical
  let aL := Finset.univ.image (leftVector ∘ a)
  let aR := Finset.univ.image (rightVector ∘ a)
  let AL := Submodule.span F2 (aL : Set BananaLimitVector)
  let AR := Submodule.span F2 (aR : Set BananaLimitVector)
  let : Finite AL := bananaLimit_finitely_generated_span_finite aL
  let : Finite AR := bananaLimit_finitely_generated_span_finite aR
  obtain ⟨al, ar, A, ea, heaL, heaR⟩ := exists_finite_banana_substructure_of_limit AL AR
  let bL := Finset.univ.image (leftVector ∘ b)
  let bR := Finset.univ.image (rightVector ∘ b)
  let S := bananaLimitCommonSupport bL bR
  let B := perfectBanana S.card
  let eb := bananaLimitBlockStandardEmbedding S
  let pL := Finset.univ.image (leftVector ∘ p)
  let pR := Finset.univ.image (rightVector ∘ p)
  have hbL (i : Fin r) :
      leftVector (b i) ∈ bananaLimitBlock S :=
    bananaLimit_left_mem_common_block bL bR _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hbR (i : Fin r) :
      rightVector (b i) ∈ bananaLimitBlock S :=
    bananaLimit_right_mem_common_block bL bR _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have factor (i : Fin l → Fin r) (g : BananaLimitAutomorphism) (hg : g • a = b ∘ i) :
      ∃ f : BananaMatrixEmbedding A B,
        (∀ x, eb.left (f.left x) = g.val.1 (ea.left x)) ∧
        (∀ y, eb.right (f.right y) = g.val.2 (ea.right y)) := by
    have hL (x : Fin al → F2) : (g • ea).left x ∈ bananaLimitBlock S := by
      have hx : ea.left x ∈ AL := heaL ▸ LinearMap.mem_range_self ea.left x
      have hSpan : AL ≤ (bananaLimitBlock S).comap g.val.1.toLinearMap := by
        apply Submodule.span_le.mpr
        intro z hz
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (show z ∈ aL from hz)
        change g.val.1 (leftVector (a u)) ∈ bananaLimitBlock S
        rw [← leftVector_smul, show g • a u = b (i u) from congrFun hg u]
        exact hbL (i u)
      exact hSpan hx
    have hR (y : Fin ar → F2) : (g • ea).right y ∈ bananaLimitBlock S := by
      have hy : ea.right y ∈ AR := heaR ▸ LinearMap.mem_range_self ea.right y
      have hSpan : AR ≤ (bananaLimitBlock S).comap g.val.2.toLinearMap := by
        apply Submodule.span_le.mpr
        intro z hz
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (show z ∈ aR from hz)
        change g.val.2 (rightVector (a u)) ∈ bananaLimitBlock S
        rw [← rightVector_smul, show g • a u = b (i u) from congrFun hg u]
        exact hbR (i u)
      exact hSpan hy
    exact ⟨(g • ea).factorToPerfectBlock S hL hR,
      (g • ea).factorToPerfectBlock_left S hL hR,
      (g • ea).factorToPerfectBlock_right S hL hR⟩
  obtain ⟨e, he⟩ := exists_bananaLimit_target_with_parameterStabilizer_transitive A B pL pR
  obtain ⟨v, hv⟩ := eb.exists_automorphism_smul_eq e
  have hvL (x : Fin S.card → F2) : v.val.1 (eb.left x) = e.left x :=
    congrArg (fun z : BananaMatrixEmbeddingToLimit B => z.left x) hv
  have hvR (y : Fin S.card → F2) : v.val.2 (eb.right y) = e.right y :=
    congrArg (fun z : BananaMatrixEmbeddingToLimit B => z.right y) hv
  have vAct : ((bananaLimit_firstOrderAut v).toEquiv : BananaTaggedCarrier → BananaTaggedCarrier) ∘ b =
      v • b := funext fun t => bananaLimit_firstOrderAut_apply v (b t)
  refine ⟨v • b, fun ψ => ?_, ?_⟩
  · rw [← vAct]
    exact (Language.StrongHomClass.realize_formula (bananaLimit_firstOrderAut v).toEquiv ψ).symm
  intro i j hi hj c
  obtain ⟨gi, hgi⟩ := hi
  obtain ⟨gj, hgj⟩ := hj
  obtain ⟨fi, hfiL, hfiR⟩ := factor i gi hgi
  obtain ⟨fj, hfjL, hfjR⟩ := factor j gj hgj
  obtain ⟨g, hgL, hgR, hg⟩ := he fi fj
  have hgP (u : Fin k) : g • p u = p u := by
    have hpL : leftVector (p u) ∈ pL := Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    have hpR : rightVector (p u) ∈ pR := Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    generalize p u = z at hpL hpR ⊢
    cases z with
    | inl x => exact congrArg Sum.inl (hgL _ hpL)
    | inr y => exact congrArg Sum.inr (hgR _ hpR)
  have hmove : g • ((v • b) ∘ i) = (v • b) ∘ j := by
    funext u
    have ui := congrFun hgi u
    have uj := congrFun hgj u
    change g • (v • b (i u)) = v • b (j u)
    rw [← show gi • a u = b (i u) from ui, ← show gj • a u = b (j u) from uj]
    cases hx : a u with
    | inl x =>
      have hxSpan : x ∈ AL := Submodule.subset_span
        (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, by simp [hx, leftVector]⟩)
      obtain ⟨w, hw⟩ := show x ∈ LinearMap.range ea.left from heaL.symm ▸ hxSpan
      rw [← hw]
      have key := congrArg (fun z : BananaMatrixEmbeddingToLimit A => z.left w) hg
      change g.val.1 (e.left (fi.left w)) = e.left (fj.left w) at key
      rw [← hvL (fi.left w), ← hvL (fj.left w), hfiL, hfjL] at key
      exact congrArg Sum.inl key
    | inr y =>
      have hySpan : y ∈ AR := Submodule.subset_span
        (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, by simp [hx, rightVector]⟩)
      obtain ⟨w, hw⟩ := show y ∈ LinearMap.range ea.right from heaR.symm ▸ hySpan
      rw [← hw]
      have key := congrArg (fun z : BananaMatrixEmbeddingToLimit A => z.right w) hg
      change g.val.2 (e.right (fi.right w)) = e.right (fj.right w) at key
      rw [← hvR (fi.right w), ← hvR (fj.right w), hfiR, hfjR] at key
      exact congrArg Sum.inr key
  simpa only [hmove] using (native_formula_realize g ((v • b) ∘ i) p hgP (φ c)).symm

/-- Matching first-order types in the concrete tagged limit are
conjugate by a native BANANA automorphism. -/
theorem bananaLimit_nativeOrbit_of_sameFormulaType
    {n : ℕ} {a b : Fin n → BananaTaggedCarrier}
    (h : SameFormulaType (L := bananaTaggedLanguage) a b) :
    ∃ g : BananaLimitAutomorphism, g • a = b := by
  obtain ⟨g, hg⟩ := exists_aut_of_sameFormulaType_of_finite_tupleOrbitRepresentatives
    bananaLimit_firstOrder_finite_tuple_orbit_representatives h
  exact ⟨bananaLimit_nativeAut g,
    funext fun i => (bananaLimit_nativeAut_smul g (a i)).trans (congrFun hg i)⟩

/-- The concrete tagged limit has the definable elementary embedding
Ramsey property in finite-tuple form. -/
theorem bananaLimit_hasDefinableTupleRamsey :
    HasDefinableTupleRamsey bananaTaggedLanguage BananaTaggedCarrier := by
  intro l r k c a b p φ
  obtain ⟨d, hd, hmono⟩ := bananaLimit_definableColouring_on_tupleOrbits a b p φ
  exact ⟨d, hd, fun i j hi hj => hmono i j
    (bananaLimit_nativeOrbit_of_sameFormulaType hi) (bananaLimit_nativeOrbit_of_sameFormulaType hj)⟩

/-- In every model of the complete theory of the tagged BANANA limit,
definable colours on elementary source copies admit a monochromatic
elementary target tuple. -/
theorem bananaTagged_completeTheory_hasDefinableTupleRamsey
    (M : Type*) [bananaTaggedLanguage.Structure M]
    [M ⊨ bananaTaggedLanguage.completeTheory BananaTaggedCarrier] :
    HasDefinableTupleRamsey bananaTaggedLanguage M := by
  have hM : BananaTaggedCarrier ≅[bananaTaggedLanguage] M :=
    Language.elementarilyEquivalent_iff.mpr fun φ =>
      (Language.realize_iff_of_model_completeTheory BananaTaggedCarrier M φ).symm
  apply HasDefinableTupleRamsey.of_elementarilyEquivalent hM bananaLimit_hasDefinableTupleRamsey
  intro n
  obtain ⟨R, hR⟩ := bananaLimit_firstOrder_finite_tuple_orbit_representatives n
  exact ⟨R, formula_type_cover_of_finset_automorphism_orbit_representatives R hR⟩

end SuccessorTree.NonPrecompact
