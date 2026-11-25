import BANANA.NonPrecompact.BananaLimitOrbitCoPrecompact
import BANANA.NonPrecompact.BananaLimitGlobalHomogeneity
import BANANA.NonPrecompact.BananaCopyDegree
import BANANA.NonPrecompact.FirstOrderExtremelyAmenableDegree

/-!
# No co-precompact extremely amenable subgroup in the BANANA limit

The native pointwise automorphism group acts transitively on each finite
embedding space. The fixed point in a colouring orbit closure gives finitely
many possible translations of each finite target. These translated targets
fit in a common perfect block of the explicit limit. Thus a co-precompact
extremely amenable subgroup would bound the finite copy Ramsey degrees,
contradicting the infinite degree of a line pair.
-/

namespace SuccessorTree.NonPrecompact

open Set MulAction

private theorem limitEmbedding_ext {l r : ℕ} {A : BananaMatrixStructure l r}
    {e f : BananaMatrixEmbeddingToLimit A}
    (hL : ∀ x, e.left x = f.left x) (hR : ∀ y, e.right y = f.right y) : e = f := by
  have eL : e.left = f.left := LinearMap.ext hL
  have eR : e.right = f.right := LinearMap.ext hR
  cases e
  cases f
  cases eL
  cases eR
  rfl

private theorem matrixEmbedding_ext {l r l' r' : ℕ}
    {A : BananaMatrixStructure l r} {B : BananaMatrixStructure l' r'}
    {e f : BananaMatrixEmbedding A B}
    (hL : ∀ x, e.left x = f.left x) (hR : ∀ y, e.right y = f.right y) : e = f := by
  have eL : e.left = f.left := LinearMap.ext hL
  have eR : e.right = f.right := LinearMap.ext hR
  cases e
  cases f
  cases eL
  cases eR
  rfl

namespace BananaMatrixEmbeddingToLimit

variable {l r : ℕ} {A : BananaMatrixStructure l r}

/-- The actual limit automorphisms act on each finite embedding space by
postcomposition on the two sorts. -/
noncomputable instance : MulAction BananaLimitAutomorphism (BananaMatrixEmbeddingToLimit A) where
  smul g e := {
    left := g.val.1.toLinearMap.comp e.left
    right := g.val.2.toLinearMap.comp e.right
    left_injective := g.val.1.injective.comp e.left_injective
    right_injective := g.val.2.injective.comp e.right_injective
    pairing_apply := fun x y => (g.property (e.left x) (e.right y)).trans (e.pairing_apply x y) }
  one_smul e := limitEmbedding_ext (fun _ => rfl) (fun _ => rfl)
  mul_smul g h e := limitEmbedding_ext (fun _ => rfl) (fun _ => rfl)

theorem isOpen_automorphism_eval (e f : BananaMatrixEmbeddingToLimit A) :
    IsOpen {g : BananaLimitAutomorphism | g • e = f} := by
  have hset : {g : BananaLimitAutomorphism | g • e = f} =
      (⋂ x : Fin l → F2, {g : BananaLimitAutomorphism | g.val.1 (e.left x) = f.left x}) ∩
      (⋂ y : Fin r → F2, {g : BananaLimitAutomorphism | g.val.2 (e.right y) = f.right y}) := by
    ext g
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
    constructor
    · intro h
      exact ⟨fun x => congrArg (fun k : BananaMatrixEmbeddingToLimit A => k.left x) h,
        fun y => congrArg (fun k : BananaMatrixEmbeddingToLimit A => k.right y) h⟩
    · rintro ⟨hL, hR⟩
      exact limitEmbedding_ext hL hR
  rw [hset]
  exact (isOpen_iInter_of_finite fun x => isOpen_bananaLimitEvaluation_left (e.left x) (f.left x)).inter
    (isOpen_iInter_of_finite fun y => isOpen_bananaLimitEvaluation_right (e.right y) (f.right y))

/-- The native pointwise action is continuous on discrete finite embeddings. -/
theorem continuous_automorphism_smul
    [TopologicalSpace (BananaMatrixEmbeddingToLimit A)]
    [DiscreteTopology (BananaMatrixEmbeddingToLimit A)] :
    ContinuousSMul BananaLimitAutomorphism (BananaMatrixEmbeddingToLimit A) := by
  constructor
  apply continuous_prod_of_discrete_right.mpr
  intro e
  apply continuous_discrete_rng.mpr
  exact isOpen_automorphism_eval e

/-- Native homogeneity makes the action transitive on the embeddings of a
given finite pairing. -/
theorem exists_automorphism_smul_eq (e f : BananaMatrixEmbeddingToLimit A) :
    ∃ g : BananaLimitAutomorphism, g • e = f := by
  obtain ⟨EL, ER, hpair, hL, hR⟩ := e.exists_global_pair_automorphism_extends f
  exact ⟨⟨(EL, ER), hpair⟩, limitEmbedding_ext hL hR⟩

private theorem automorphism_smul_comp {l' r' : ℕ} {B : BananaMatrixStructure l' r'}
    (g : BananaLimitAutomorphism) (e : BananaMatrixEmbeddingToLimit B)
    (p : BananaMatrixEmbedding A B) : g • (e.comp p) = (g • e).comp p :=
  limitEmbedding_ext (fun _ => rfl) (fun _ => rfl)

private theorem factor_comp {l' r' : ℕ} {B : BananaMatrixStructure l' r'}
    (e : BananaMatrixEmbeddingToLimit B) (p : BananaMatrixEmbedding A B) (S : Finset ℚ)
    (hL : ∀ x, e.left x ∈ bananaLimitBlock S) (hR : ∀ y, e.right y ∈ bananaLimitBlock S) :
    (e.comp p).factorToPerfectBlock S (fun x => hL (p.left x)) (fun y => hR (p.right y)) =
      (e.factorToPerfectBlock S hL hR).comp p := by
  apply matrixEmbedding_ext
  · intro x
    apply (bananaLimitBlockStandardEmbedding S).left_injective
    exact ((e.comp p).factorToPerfectBlock_left S _ _ x).trans
      (e.factorToPerfectBlock_left S hL hR (p.left x)).symm
  · intro y
    apply (bananaLimitBlockStandardEmbedding S).right_injective
    exact ((e.comp p).factorToPerfectBlock_right S _ _ y).trans
      (e.factorToPerfectBlock_right S hL hR (p.right y)).symm

end BananaMatrixEmbeddingToLimit

open BananaMatrixEmbeddingToLimit

/-- The finite age of the actual BANANA limit would have finite copy degrees
if its pointwise automorphism group had a co-precompact extremely amenable
subgroup. The colours here are on genuine two-sort ranges. -/
theorem BananaMatrixStructure.finiteCopyDegree_of_coprecompactExtremelyAmenable
    {l r : ℕ} (A : BananaMatrixStructure l r)
    (H : Subgroup BananaLimitAutomorphism) (hH : CoPrecompact BananaLimitAutomorphism H)
    (hfixed : CompactFlowFixedPoint.{0, 0} H) : ∃ d : ℕ, A.copyRamseyDegreeLE d := by
  classical
  obtain ⟨e⟩ := A.embeds_in_explicit_limit
  obtain ⟨R, hR⟩ := exists_finset_orbitRepresentatives_of_coprecompact H hH e
    (e.isOpen_automorphism_eval e) e.exists_automorphism_smul_eq
  refine ⟨R.card, fun lB rB B numColours hColours => ?_⟩
  obtain ⟨b⟩ := B.embeds_in_explicit_limit
  letI : TopologicalSpace (BananaMatrixEmbeddingToLimit A) := ⊥
  letI : DiscreteTopology (BananaMatrixEmbeddingToLimit A) := ⟨rfl⟩
  letI : ContinuousSMul BananaLimitAutomorphism (BananaMatrixEmbeddingToLimit A) :=
    continuous_automorphism_smul
  letI : TopologicalSpace (Fin numColours) := ⊥
  letI : DiscreteTopology (Fin numColours) := ⟨rfl⟩
  letI : Finite (BananaMatrixEmbedding A B) :=
    Finite.of_injective (fun f : BananaMatrixEmbedding A B =>
      ((f.left : (Fin l → F2) → (Fin lB → F2)), (f.right : (Fin r → F2) → (Fin rB → F2))))
      (fun _ _ h => matrixEmbedding_ext (congrFun (congrArg Prod.fst h))
        (congrFun (congrArg Prod.snd h)))
  letI : Fintype (BananaMatrixEmbedding A B) := Fintype.ofFinite _
  let T : Finset (BananaMatrixEmbeddingToLimit A) := Finset.univ.image b.comp
  obtain ⟨K, hK⟩ := exists_finite_translates_of_orbit_fixed_colourings (G := H)
    (Colour := Fin numColours) T R hR (fun c => exists_fixed_colouring_in_orbit_closure hfixed c)
  let left : Finset BananaLimitVector := K.biUnion fun g =>
    (Finset.univ : Finset (Fin lB → F2)).image ((g : BananaLimitAutomorphism) • b).left
  let right : Finset BananaLimitVector := K.biUnion fun g =>
    (Finset.univ : Finset (Fin rB → F2)).image ((g : BananaLimitAutomorphism) • b).right
  let S := bananaLimitCommonSupport left right
  refine ⟨S.card, S.card, perfectBanana S.card, fun c => ?_⟩
  let padded (f : BananaMatrixEmbeddingToLimit A) : Fin numColours :=
    if h : (∀ x, f.left x ∈ bananaLimitBlock S) ∧ (∀ y, f.right y ∈ bananaLimitBlock S) then
      c (f.factorToPerfectBlock S h.1 h.2).copyRanges
    else ⟨0, hColours⟩
  obtain ⟨g, hg, palette, hCard, hPalette⟩ := hK padded
  let moved : BananaMatrixEmbeddingToLimit B := (g : BananaLimitAutomorphism) • b
  have hL (x : Fin lB → F2) : moved.left x ∈ bananaLimitBlock S :=
    bananaLimit_left_mem_common_block left right (moved.left x)
      (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩)
  have hR' (y : Fin rB → F2) : moved.right y ∈ bananaLimitBlock S :=
    bananaLimit_right_mem_common_block left right (moved.right y)
      (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩⟩)
  let f := moved.factorToPerfectBlock S hL hR'
  refine ⟨f, palette, hCard, fun D => ?_⟩
  obtain ⟨p, hpL, hpR⟩ := D.property
  have hD : D = p.copyRanges := Subtype.ext (Prod.ext hpL hpR)
  have hp := hPalette (b.comp p) (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩)
  change padded ((g : BananaLimitAutomorphism) • b.comp p) ∈ palette at hp
  rw [automorphism_smul_comp] at hp
  have hS : (∀ x, (moved.comp p).left x ∈ bananaLimitBlock S) ∧
      (∀ y, (moved.comp p).right y ∈ bananaLimitBlock S) :=
    ⟨fun x => hL (p.left x), fun y => hR' (p.right y)⟩
  change padded (moved.comp p) ∈ palette at hp
  dsimp only [padded] at hp
  rw [dite_eq_left hS] at hp
  rw [hD, p.copyRanges_comp]
  rw [factor_comp moved p S hL hR'] at hp
  exact hp

/-- The actual pointwise automorphism group of the native BANANA pairing
has no co-precompact extremely amenable subgroup. -/
theorem bananaLimit_no_coprecompact_extremelyAmenable :
    ¬ ∃ H : Subgroup BananaLimitAutomorphism,
      CoPrecompact BananaLimitAutomorphism H ∧ CompactFlowFixedPoint.{0, 0} H := by
  rintro ⟨H, hH, hfixed⟩
  obtain ⟨d, hd⟩ := (linePairSource (0 : F2)).finiteCopyDegree_of_coprecompactExtremelyAmenable
    H hH hfixed
  exact (linePairSource (0 : F2)).copyRamseyDegree_infinite_of_positive
    (by decide) (by decide) d hd

/-- An oligomorphic subgroup of the native BANANA group cannot be
extremely amenable. -/
theorem bananaLimit_not_extremelyAmenable_of_finite_taggedTupleOrbitRepresentatives
    (H : Subgroup BananaLimitAutomorphism)
    (hH : ∀ n : ℕ, ∃ R : Finset (BananaLimitTaggedTuple n),
      ∀ x : BananaLimitTaggedTuple n, ∃ r ∈ R, x ∈ orbit H r) :
    ¬ CompactFlowFixedPoint.{0, 0} H :=
  fun hfixed => bananaLimit_no_coprecompact_extremelyAmenable
    ⟨H, bananaLimit_coprecompact_of_finite_taggedTupleOrbitRepresentatives H hH, hfixed⟩

end SuccessorTree.NonPrecompact
