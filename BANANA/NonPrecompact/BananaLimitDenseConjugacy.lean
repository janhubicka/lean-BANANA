import BANANA.NonPrecompact.BananaFiniteSystemsJepWap
import BANANA.NonPrecompact.BananaLimitGlobalHomogeneity
import BANANA.NonPrecompact.BananaLimitOrbitCoPrecompact
import BANANA.NonPrecompact.BananaLimitPolish
import BANANA.NonPrecompact.DenseOrbitsOfTransitiveAction
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Dynamics.Transitive
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Dense diagonal conjugacy orbits in the BANANA limit

The joint embedding property of standard perfect-total finite systems
gives topological transitivity of diagonal conjugation on every finite
power of the native pointwise automorphism group.
-/

namespace SuccessorTree.NonPrecompact
open Set Filter Topology
open scoped Pointwise

private abbrev NativeTuple (n : ℕ) := Fin n → BananaLimitAutomorphism

private def Realises {n : ℕ} (t : NativeTuple n) (P : BananaStandardPerfectSystem n)
    (e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension)) : Prop :=
  (∀ i x, (t i).val.1 (e.left x) = e.left ((P.actions i).left x)) ∧
  (∀ i y, (t i).val.2 (e.right y) = e.right ((P.actions i).right y))

private noncomputable def nativeBlockGL (S : Finset ℚ) (a : FinitePerfectGL S.card) :
    BananaLimitAutomorphism :=
  ⟨bananaLimitFiniteGLAction S a, bananaLimitFiniteGLAction_pairing S a⟩

private theorem blockGL_realises {n : ℕ} (S : Finset ℚ)
    (a : Fin n → FinitePerfectGL S.card) :
    Realises (fun i => nativeBlockGL S (a i))
      ⟨S.card, fun i => (a i).toPerfectPairAutomorphism⟩
      (bananaLimitBlockStandardEmbedding S) :=
  ⟨fun i x => bananaLimitFiniteGLAction_left_on_block S (a i) x,
   fun i y => bananaLimitFiniteGLAction_right_on_block S (a i) y⟩

private theorem exists_block_realises {n : ℕ} (P : BananaStandardPerfectSystem n) :
    ∃ (t : NativeTuple n) (e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension)),
      Realises t P e := by
  rcases P with ⟨d, f⟩
  obtain ⟨S, hS⟩ := exists_rational_coordinates d
  subst d
  let a (i : Fin n) := (f i).leftSelfEquiv
  refine ⟨fun i => nativeBlockGL S (a i), bananaLimitBlockStandardEmbedding S, ?_⟩
  constructor
  · intro i x
    exact bananaLimitFiniteGLAction_left_on_block S (a i) x
  · intro i y
    change (nativeBlockGL S (a i)).val.2 ((bananaLimitBlockStandardEmbedding S).right y) =
      (bananaLimitBlockStandardEmbedding S).right ((f i).right y)
    rw [(f i).right_eq_dotContragredient_leftSelfEquiv]
    exact bananaLimitFiniteGLAction_right_on_block S (a i) y

private theorem Realises.comp {n : ℕ} {t : NativeTuple n} {Q : BananaStandardPerfectSystem n}
    {e : BananaMatrixEmbeddingToLimit (perfectBanana Q.dimension)}
    (ht : Realises t Q e) {P : BananaStandardPerfectSystem n}
    (f : BananaStandardPerfectSystem.Embedding P Q) :
    Realises t P (e.comp f.carrier) := by
  constructor
  · intro i x
    change (t i).val.1 (e.left (f.carrier.left x)) =
      e.left (f.carrier.left ((P.actions i).left x))
    rw [ht.1, f.intertwines_left]
  · intro i y
    change (t i).val.2 (e.right (f.carrier.right y)) =
      e.right (f.carrier.right ((P.actions i).right y))
    rw [ht.2, f.intertwines_right]

private theorem Realises.exists_conj {n : ℕ} {t : NativeTuple n} {P : BananaStandardPerfectSystem n}
    {e' : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension)}
    (ht : Realises t P e') (e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension)) :
    ∃ k : ConjAct BananaLimitAutomorphism, Realises (k • t) P e := by
  obtain ⟨kL, kR, hpair, hL, hR⟩ := e.exists_global_pair_automorphism_extends e'
  let k : BananaLimitAutomorphism := ⟨(kL, kR), hpair⟩
  refine ⟨ConjAct.toConjAct k⁻¹, ?_, ?_⟩
  · intro i x
    change kL.symm ((t i).val.1 (kL (e.left x))) = e.left ((P.actions i).left x)
    rw [hL, ht.1, ← hL, LinearEquiv.symm_apply_apply]
  · intro i y
    change kR.symm ((t i).val.2 (kR (e.right y))) = e.right ((P.actions i).right y)
    rw [hR, ht.2, ← hR, LinearEquiv.symm_apply_apply]

private theorem exists_system_neighbourhood {n : ℕ} {U : Set (NativeTuple n)}
    (hU : IsOpen U) (hUn : U.Nonempty) :
    ∃ P : BananaStandardPerfectSystem n,
    ∃ e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension),
      ∀ t, Realises t P e → t ∈ U := by
  classical
  obtain ⟨g, hg⟩ := hUn
  have hN := hU.mem_nhds hg
  rw [nhds_pi, Filter.mem_pi'] at hN
  obtain ⟨I, V, hV, hVU⟩ := hN
  choose m a ha using fun i =>
    exists_bananaLimitTaggedTupleEval_subset_of_mem_nhds (g i) (V i) (hV i)
  let vectors (i : Fin n) : Finset BananaLimitVector :=
    Finset.univ.image (fun j : Fin (m i) => Sum.elim id id (a i j))
  let tests : Finset BananaLimitVector := Finset.univ.biUnion vectors
  have htests (i : Fin n) (j : Fin (m i)) :
      Sum.elim id id (a i j) ∈ tests :=
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  choose T p hpL hpR using fun i => exists_finiteGLAction_agree_on_finite_sets
    (g i).val.1 (g i).val.2 (g i).property tests tests
  let S := bananaLimitCommonSupport tests tests ∪ Finset.univ.biUnion T
  have hTS (i : Fin n) : T i ⊆ S := fun z hz =>
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩)
  choose q hqL hqR using fun i =>
    exists_bananaLimitFiniteGLAction_larger_stage (T i) S (hTS i) (p i)
  let e := bananaLimitBlockStandardEmbedding S
  let P : BananaStandardPerfectSystem n :=
    ⟨S.card, fun i => (q i).toPerfectPairAutomorphism⟩
  have hreal : Realises (fun i => nativeBlockGL S (q i)) P e := blockGL_realises S q
  have hinBlock {z : BananaLimitVector} (hz : z ∈ tests) : z ∈ bananaLimitBlock S := by
    apply bananaLimitBlock_mono Finset.subset_union_left
    exact bananaLimit_left_mem_common_block tests tests z hz
  refine ⟨P, e, fun t ht => hVU ?_⟩
  intro i _
  apply ha i
  change t i • a i = g i • a i
  funext j
  change t i • a i j = g i • a i j
  have hj := htests i j
  generalize heq : a i j = u at hj ⊢
  cases u with
  | inl z =>
    obtain ⟨x, hx⟩ := bananaLimitBlockStandardEmbedding_surjective_on_block S z (hinBlock hj)
    have hx' : e.left x = z := hx
    have hmatch : (t i).val.1 z = (bananaLimitFiniteGLAction S (q i)).1 z := by
      rw [← hx', ht.1 i x, ← hreal.1 i x]
      rfl
    change Sum.inl ((t i).val.1 z) = Sum.inl ((g i).val.1 z)
    rw [hmatch, hqL, hpL i z hj]
  | inr z =>
    obtain ⟨y, hy⟩ := bananaLimitBlockStandardEmbedding_surjective_on_block S z (hinBlock hj)
    have hyr : e.right y = z := hy
    have hmatch : (t i).val.2 z = (bananaLimitFiniteGLAction S (q i)).2 z := by
      rw [← hyr, ht.2 i y, ← hreal.2 i y]
      rfl
    change Sum.inr ((t i).val.2 z) = Sum.inr ((g i).val.2 z)
    rw [hmatch, hqR, hpR i z hj]

/-- Diagonal conjugation on each finite power of the native pointwise
BANANA automorphism group is topologically transitive. -/
theorem bananaLimit_diagonalConjugation_topologicallyTransitive (n : ℕ) :
    MulAction.IsTopologicallyTransitive (ConjAct BananaLimitAutomorphism)
      (Fin n → BananaLimitAutomorphism) := by
  constructor
  intro U V hU hUn hV hVn
  obtain ⟨P, e, hP⟩ := exists_system_neighbourhood hU hUn
  obtain ⟨Q, f, hQ⟩ := exists_system_neighbourhood hV hVn
  obtain ⟨R, ⟨p⟩, ⟨q⟩⟩ := BananaStandardPerfectSystem.exists_joint_embedding P Q
  obtain ⟨t, r, hr⟩ := exists_block_realises R
  obtain ⟨k, hk⟩ := (hr.comp p).exists_conj e
  obtain ⟨l, hl⟩ := (hr.comp q).exists_conj f
  refine ⟨l * k⁻¹, l • t, ?_, hQ _ hl⟩
  refine ⟨k • t, hP _ hk, ?_⟩
  change (l * k⁻¹) • (k • t) = l • t
  rw [smul_smul, inv_mul_cancel_right]

private theorem continuous_diagonalConjugation (n : ℕ) :
    ContinuousConstSMul (ConjAct BananaLimitAutomorphism) (NativeTuple n) := by
  constructor
  intro g
  apply continuous_pi
  intro i
  change Continuous (fun t : NativeTuple n => ConjAct.ofConjAct g * t i * (ConjAct.ofConjAct g)⁻¹)
  exact (continuous_const.mul (continuous_apply i)).mul continuous_const

/-- Every finite power of the native BANANA automorphism group has a dense
orbit under simultaneous conjugation. -/
theorem bananaLimit_exists_dense_diagonalConjugacyOrbit (n : ℕ) :
    ∃ t : Fin n → BananaLimitAutomorphism,
      Dense (MulAction.orbit (ConjAct BananaLimitAutomorphism) t) := by
  let := bananaLimitAutomorphism_polishSpace
  let := continuous_diagonalConjugation n
  let := bananaLimit_diagonalConjugation_topologicallyTransitive n
  exact exists_dense_orbit_of_topologicallyTransitive (ConjAct BananaLimitAutomorphism)

/-- The native tuples with dense diagonal conjugacy orbit form a comeagre set. -/
theorem bananaLimit_dense_diagonalConjugacyOrbit_points_mem_residual (n : ℕ) :
    {t : Fin n → BananaLimitAutomorphism |
      Dense (MulAction.orbit (ConjAct BananaLimitAutomorphism) t)} ∈ residual _ := by
  let := bananaLimitAutomorphism_polishSpace
  let := continuous_diagonalConjugation n
  let := bananaLimit_diagonalConjugation_topologicallyTransitive n
  exact dense_orbit_points_mem_residual (ConjAct BananaLimitAutomorphism)

end SuccessorTree.NonPrecompact
