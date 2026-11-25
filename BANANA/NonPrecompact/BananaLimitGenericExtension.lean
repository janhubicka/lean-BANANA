import BANANA.NonPrecompact.BananaLimitDenseConjugacy
import BANANA.NonPrecompact.BananaLimitExtremelyAmenableDegree

/-!
# Perfect-system extension conditions for native BANANA automorphisms

A tuple is rich when its finite subsets are covered by realised perfect
systems, and every embedded perfect system extends along every embedding
into a larger perfect system. Each individual condition is dense and open.
-/

namespace SuccessorTree.NonPrecompact

open Set Filter Topology
open scoped Pointwise

namespace BananaNativeTuple

variable {n : ℕ}

/-- Every pair of finite sets is covered by an embedded invariant perfect system. -/
def Covers (t : BananaNativeTuple n) : Prop :=
  ∀ (L R : Finset BananaLimitVector),
    ∃ (P : BananaStandardPerfectSystem n)
      (e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension)),
      BananaPerfectSystemRealises t P e ∧
        (↑L : Set BananaLimitVector) ⊆ Set.range e.left ∧
        (↑R : Set BananaLimitVector) ⊆ Set.range e.right

/-- Every embedded invariant perfect system extends along a finite system embedding. -/
def Extends (t : BananaNativeTuple n) : Prop :=
  ∀ (P Q : BananaStandardPerfectSystem n) (f : BananaStandardPerfectSystem.Embedding P Q)
    (e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension)),
    BananaPerfectSystemRealises t P e →
      ∃ g : BananaMatrixEmbeddingToLimit (perfectBanana Q.dimension),
        BananaPerfectSystemRealises t Q g ∧
          (∀ x, g.left (f.carrier.left x) = e.left x) ∧
          (∀ y, g.right (f.carrier.right y) = e.right y)

/-- Invariant perfect systems cover all points and have the finite extension property. -/
def IsRich (t : BananaNativeTuple n) : Prop :=
  Covers t ∧ Extends t

local instance genericExtensionVectorTopology : TopologicalSpace BananaLimitVector := ⊥
local instance genericExtensionVectorDiscrete : DiscreteTopology BananaLimitVector := ⟨rfl⟩

/-- A specified embedded finite system is realised on a clopen set of tuples. -/
theorem isClopen_realises (P : BananaStandardPerfectSystem n)
    (e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension)) :
    IsClopen {t : BananaNativeTuple n | BananaPerfectSystemRealises t P e} := by
  let L (i : Fin n) (x : Fin P.dimension → F2) : Set (BananaNativeTuple n) :=
    {t | (t i).val.1 (e.left x) = e.left ((P.actions i).left x)}
  let R (i : Fin n) (y : Fin P.dimension → F2) : Set (BananaNativeTuple n) :=
    {t | (t i).val.2 (e.right y) = e.right ((P.actions i).right y)}
  have hL (i : Fin n) (x : Fin P.dimension → F2) : IsClopen (L i x) :=
    (isClopen_discrete {e.left ((P.actions i).left x)}).preimage
      ((continuous_bananaLimitEvaluation (.inl (e.left x))).comp (continuous_apply i))
  have hR (i : Fin n) (y : Fin P.dimension → F2) : IsClopen (R i y) :=
    (isClopen_discrete {e.right ((P.actions i).right y)}).preimage
      ((continuous_bananaLimitEvaluation (.inr (e.right y))).comp (continuous_apply i))
  have hs : {t : BananaNativeTuple n | BananaPerfectSystemRealises t P e} =
      (⋂ i, ⋂ x, L i x) ∩ (⋂ i, ⋂ y, R i y) := by
    ext
    simp [BananaPerfectSystemRealises, L, R]
  rw [hs]
  exact ⟨(isClosed_iInter fun i => isClosed_iInter fun x => (hL i x).1).inter
      (isClosed_iInter fun i => isClosed_iInter fun y => (hR i y).1),
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun x => (hL i x).2).inter
      (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun y => (hR i y).2)⟩

/-- Agreement with some invariant perfect system covering the specified finite sets. -/
def coverageCondition (L R : Finset BananaLimitVector) : Set (BananaNativeTuple n) :=
  {t | ∃ (P : BananaStandardPerfectSystem n)
      (e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension)),
    BananaPerfectSystemRealises t P e ∧
      (↑L : Set BananaLimitVector) ⊆ Set.range e.left ∧
      (↑R : Set BananaLimitVector) ⊆ Set.range e.right}

theorem isOpen_coverageCondition (L R : Finset BananaLimitVector) :
    IsOpen (coverageCondition (n := n) L R) := by
  have hset : coverageCondition (n := n) L R =
      ⋃ (P : BananaStandardPerfectSystem n)
        (e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension))
        (_ : (↑L : Set BananaLimitVector) ⊆ Set.range e.left ∧
          (↑R : Set BananaLimitVector) ⊆ Set.range e.right),
        {t : BananaNativeTuple n | BananaPerfectSystemRealises t P e} := by
    ext t
    simp only [coverageCondition, mem_ofPred_eq, mem_iUnion]
    aesop
  rw [hset]
  exact isOpen_iUnion fun P => isOpen_iUnion fun e => isOpen_iUnion fun _ =>
    (isClopen_realises P e).2

theorem dense_coverageCondition (L R : Finset BananaLimitVector) :
    Dense (coverageCondition (n := n) L R) := by
  rw [dense_iff_inter_open]
  intro U hU hUn
  obtain ⟨S, hS, a, hs⟩ := exists_bananaPerfectSystem_neighbourhood hU hUn
    (bananaLimitCommonSupport L R)
  have ha := bananaNativeBlockGL_realises S a
  refine ⟨_, hs _ ha, ⟨⟨S.card, fun i => (a i).toPerfectPairAutomorphism⟩,
    bananaLimitBlockStandardEmbedding S, ha, ?_, ?_⟩⟩
  · intro x hx
    exact bananaLimitBlockStandardEmbedding_surjective_on_block S x
      ((bananaLimitBlock_mono hS) (bananaLimit_left_mem_common_block L R x hx))
  · intro y hy
    exact bananaLimitBlockStandardEmbedding_surjective_on_block S y
      ((bananaLimitBlock_mono hS) (bananaLimit_right_mem_common_block L R y hy))

/-- A specific possible extension of a specified embedded perfect system is required. -/
def extensionCondition (P Q : BananaStandardPerfectSystem n)
    (f : BananaStandardPerfectSystem.Embedding P Q)
    (e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension)) :
    Set (BananaNativeTuple n) :=
  {t | ¬ BananaPerfectSystemRealises t P e ∨
      ∃ g : BananaMatrixEmbeddingToLimit (perfectBanana Q.dimension),
        BananaPerfectSystemRealises t Q g ∧
          (∀ x, g.left (f.carrier.left x) = e.left x) ∧
          (∀ y, g.right (f.carrier.right y) = e.right y)}

theorem isOpen_extensionCondition (P Q : BananaStandardPerfectSystem n)
    (f : BananaStandardPerfectSystem.Embedding P Q)
    (e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension)) :
    IsOpen (extensionCondition P Q f e) := by
  have hset : extensionCondition P Q f e =
      {t : BananaNativeTuple n | BananaPerfectSystemRealises t P e}ᶜ ∪
        ⋃ (g : BananaMatrixEmbeddingToLimit (perfectBanana Q.dimension))
          (_ : (∀ x, g.left (f.carrier.left x) = e.left x) ∧
            (∀ y, g.right (f.carrier.right y) = e.right y)),
          {t : BananaNativeTuple n | BananaPerfectSystemRealises t Q g} := by
    ext t
    simp only [extensionCondition, mem_ofPred_eq, mem_union, mem_compl_iff, mem_iUnion]
    aesop
  rw [hset]
  exact (isClopen_realises P e).1.isOpen_compl.union
    (isOpen_iUnion fun g => isOpen_iUnion fun _ => (isClopen_realises Q g).2)

private theorem realises_conj {P : BananaStandardPerfectSystem n}
    {t : BananaNativeTuple n} {e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension)}
    (ht : BananaPerfectSystemRealises t P e) (k : BananaLimitAutomorphism) :
    BananaPerfectSystemRealises ((ConjAct.toConjAct k) • t) P (k • e) := by
  constructor
  · intro i x
    change k.val.1 ((t i).val.1 (k.val.1.symm (k.val.1 (e.left x)))) =
      k.val.1 (e.left ((P.actions i).left x))
    rw [LinearEquiv.symm_apply_apply, ht.1]
  · intro i y
    change k.val.2 ((t i).val.2 (k.val.2.symm (k.val.2 (e.right y)))) =
      k.val.2 (e.right ((P.actions i).right y))
    rw [LinearEquiv.symm_apply_apply, ht.2]

private noncomputable def factorSystem {P : BananaStandardPerfectSystem n} {t : BananaNativeTuple n}
    {e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension)}
    (he : BananaPerfectSystemRealises t P e) (S : Finset ℚ)
    (a : Fin n → FinitePerfectGL S.card)
    (ht : BananaPerfectSystemRealises t ⟨S.card, fun i => (a i).toPerfectPairAutomorphism⟩
      (bananaLimitBlockStandardEmbedding S))
    (hL : ∀ x, e.left x ∈ bananaLimitBlock S) (hR : ∀ y, e.right y ∈ bananaLimitBlock S) :
    BananaStandardPerfectSystem.Embedding P ⟨S.card, fun i => (a i).toPerfectPairAutomorphism⟩ where
  carrier := e.factorToPerfectBlock S hL hR
  intertwines_left := by
    intro i x
    apply (bananaLimitBlockStandardEmbedding S).left_injective
    rw [← ht.1, e.factorToPerfectBlock_left, e.factorToPerfectBlock_left, he.1]
  intertwines_right := by
    intro i y
    apply (bananaLimitBlockStandardEmbedding S).right_injective
    rw [← ht.2, e.factorToPerfectBlock_right, e.factorToPerfectBlock_right, he.2]

/-- Given any nonempty pointwise neighbourhood, amalgamate a finite system
inside it with the demanded extension and identify the neighbourhood's
finite block by a native automorphism. -/
theorem dense_extensionCondition (P Q : BananaStandardPerfectSystem n)
    (f : BananaStandardPerfectSystem.Embedding P Q)
    (e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension)) :
    Dense (extensionCondition P Q f e) := by
  classical
  rw [dense_iff_inter_open]
  intro U hU hUn
  by_cases havoid : ∃ t ∈ U, ¬ BananaPerfectSystemRealises t P e
  · obtain ⟨t, ht, he⟩ := havoid
    exact ⟨t, ht, Or.inl he⟩
  push Not at havoid
  let L := Finset.univ.image e.left
  let R := Finset.univ.image e.right
  obtain ⟨S, hS, a, hUS⟩ := exists_bananaPerfectSystem_neighbourhood hU hUn
    (bananaLimitCommonSupport L R)
  let T : BananaStandardPerfectSystem n := ⟨S.card, fun i => (a i).toPerfectPairAutomorphism⟩
  let b := bananaLimitBlockStandardEmbedding S
  have ha := bananaNativeBlockGL_realises S a
  have he := havoid _ (hUS _ ha)
  have hL (x : Fin P.dimension → F2) : e.left x ∈ bananaLimitBlock S :=
    (bananaLimitBlock_mono hS) (bananaLimit_left_mem_common_block L R _ (Finset.mem_image_of_mem _ (Finset.mem_univ x)))
  have hR (y : Fin P.dimension → F2) : e.right y ∈ bananaLimitBlock S :=
    (bananaLimitBlock_mono hS) (bananaLimit_right_mem_common_block L R _ (Finset.mem_image_of_mem _ (Finset.mem_univ y)))
  let p : BananaStandardPerfectSystem.Embedding P T := factorSystem he S a ha hL hR
  obtain ⟨D, h, j, hj⟩ := BananaStandardPerfectSystem.exists_amalgam P T Q p f
  obtain ⟨t, d, hd⟩ := exists_bananaNativeBlock_realises D
  obtain ⟨k, hk⟩ := (d.comp h.carrier).exists_automorphism_smul_eq b
  let u : BananaNativeTuple n := ConjAct.toConjAct k • t
  have hud : BananaPerfectSystemRealises u D (k • d) := realises_conj hd k
  have hub : BananaPerfectSystemRealises u T b := by
    rw [← hk]
    exact hud.comp h
  refine ⟨u, hUS _ hub, Or.inr ⟨(k • d).comp j.carrier, hud.comp j, ?_, ?_⟩⟩
  · intro x
    have hleft := hj.1 x
    change h.carrier.left (p.carrier.left x) = j.carrier.left (f.carrier.left x) at hleft
    change (k • d).left (j.carrier.left (f.carrier.left x)) = e.left x
    rw [← hleft]
    exact (congrArg (fun (v : BananaMatrixEmbeddingToLimit (perfectBanana T.dimension)) =>
      v.left (p.carrier.left x)) hk).trans (e.factorToPerfectBlock_left S hL hR x)
  · intro y
    have hright := hj.2 y
    change h.carrier.right (p.carrier.right y) = j.carrier.right (f.carrier.right y) at hright
    change (k • d).right (j.carrier.right (f.carrier.right y)) = e.right y
    rw [← hright]
    exact (congrArg (fun (v : BananaMatrixEmbeddingToLimit (perfectBanana T.dimension)) =>
      v.right (p.carrier.right y)) hk).trans (e.factorToPerfectBlock_right S hL hR y)

private theorem matrixEmbedding_countable
    {l r l' r' : ℕ} (A : BananaMatrixStructure l r) (B : BananaMatrixStructure l' r') :
    Countable (BananaMatrixEmbedding A B) := by
  refine Function.Injective.countable (f := fun e : BananaMatrixEmbedding A B =>
    ((e.left : (Fin l → F2) → (Fin l' → F2)),
     (e.right : (Fin r → F2) → (Fin r' → F2)))) ?_
  intro f g h
  have hl : f.left = g.left := LinearMap.ext (congrFun (congrArg Prod.fst h))
  have hr : f.right = g.right := LinearMap.ext (congrFun (congrArg Prod.snd h))
  cases f
  cases g
  cases hl
  cases hr
  rfl

private theorem perfectSystem_countable (n : ℕ) : Countable (BananaStandardPerfectSystem n) := by
  let (d : ℕ) := matrixEmbedding_countable (perfectBanana d) (perfectBanana d)
  let decode (s : Σ d : ℕ, Fin n →
      BananaMatrixEmbedding (perfectBanana d) (perfectBanana d)) : BananaStandardPerfectSystem n :=
    ⟨s.1, s.2⟩
  refine Function.Injective.countable (f := fun P : BananaStandardPerfectSystem n =>
    (⟨P.dimension, P.actions⟩ : Σ d : ℕ, Fin n →
      BananaMatrixEmbedding (perfectBanana d) (perfectBanana d))) ?_
  intro P Q h
  exact congrArg decode h

private theorem systemEmbedding_countable (P Q : BananaStandardPerfectSystem n) :
    Countable (BananaStandardPerfectSystem.Embedding P Q) := by
  let := matrixEmbedding_countable (perfectBanana P.dimension) (perfectBanana Q.dimension)
  refine Function.Injective.countable (f := BananaStandardPerfectSystem.Embedding.carrier) ?_
  intro f g h
  cases f
  cases g
  cases h
  rfl

private theorem limitEmbedding_countable
    {l r : ℕ} (A : BananaMatrixStructure l r) : Countable (BananaMatrixEmbeddingToLimit A) := by
  refine Function.Injective.countable (f := fun e : BananaMatrixEmbeddingToLimit A =>
    ((e.left : (Fin l → F2) → BananaLimitVector),
     (e.right : (Fin r → F2) → BananaLimitVector))) ?_
  intro f g h
  have hl : f.left = g.left := LinearMap.ext (congrFun (congrArg Prod.fst h))
  have hr : f.right = g.right := LinearMap.ext (congrFun (congrArg Prod.snd h))
  cases f
  cases g
  cases hl
  cases hr
  rfl

/-- The rich native tuples form a residual set, by the countable intersections
of coverage and extension conditions. -/
theorem rich_mem_residual (n : ℕ) :
    {t : BananaNativeTuple n | IsRich t} ∈ residual _ := by
  classical
  let := perfectSystem_countable n
  have hcover : ∀ᶠ t : BananaNativeTuple n in residual _, Covers t := by
    unfold Covers
    rw [eventually_countable_forall]
    intro L
    rw [eventually_countable_forall]
    intro R
    exact residual_of_dense_open (isOpen_coverageCondition L R) (dense_coverageCondition L R)
  have hext : ∀ᶠ t : BananaNativeTuple n in residual _, Extends t := by
    unfold Extends
    rw [eventually_countable_forall]
    intro P
    rw [eventually_countable_forall]
    intro Q
    let := systemEmbedding_countable P Q
    rw [eventually_countable_forall]
    intro f
    let := limitEmbedding_countable (perfectBanana P.dimension)
    rw [eventually_countable_forall]
    intro e
    have hc := residual_of_dense_open (isOpen_extensionCondition P Q f e)
      (dense_extensionCondition P Q f e)
    filter_upwards [hc] with t ht hP
    rcases ht with hP' | h
    · exact (hP' hP).elim
    · exact h
  exact hcover.and hext

end BananaNativeTuple

end SuccessorTree.NonPrecompact
