import BANANA.NonPrecompact.BananaLimitGenericExtension
import Mathlib.Order.Ideal

/-!
# Conjugacy from perfect-system back-and-forth

For two tuples of automorphisms, a finite partial conjugacy consists of
two realisations of the same perfect system. Finite perfect-system
coverage and relative extension make the four families of point
requirements cofinal. A chain meeting all four families yields a
pairing-preserving automorphism which conjugates the tuples.
-/

namespace SuccessorTree.NonPrecompact

open Filter Topology

private theorem factorLinearMap {V W : Type}
    [AddCommGroup V] [AddCommGroup W] [Module F2 V] [Module F2 W]
    (f : V →ₗ[F2] BananaLimitVector) (g : W →ₗ[F2] BananaLimitVector)
    (hg : Function.Injective g) (h : Set.range f ⊆ Set.range g) :
    ∃ u : V →ₗ[F2] W, ∀ x, g (u x) = f x := by
  let gIso := LinearEquiv.ofInjective g hg
  let fRange := f.codRestrict (LinearMap.range g) fun x => h ⟨x, rfl⟩
  refine ⟨gIso.symm.toLinearMap.comp fRange, fun x => ?_⟩
  change (gIso (gIso.symm (fRange x))).val = f x
  rw [LinearEquiv.apply_symm_apply]
  rfl

private theorem realisesFactor {n : ℕ} {t : BananaNativeTuple n}
    {P Q : BananaStandardPerfectSystem n}
    {e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension)}
    {g : BananaMatrixEmbeddingToLimit (perfectBanana Q.dimension)}
    (he : BananaPerfectSystemRealises t P e) (hg : BananaPerfectSystemRealises t Q g)
    (hL : Set.range e.left ⊆ Set.range g.left)
    (hR : Set.range e.right ⊆ Set.range g.right) :
    ∃ f : BananaStandardPerfectSystem.Embedding P Q,
      (∀ x, g.left (f.carrier.left x) = e.left x) ∧
      (∀ y, g.right (f.carrier.right y) = e.right y) := by
  obtain ⟨l, hl⟩ := factorLinearMap e.left g.left g.left_injective hL
  obtain ⟨r, hr⟩ := factorLinearMap e.right g.right g.right_injective hR
  let carrier : BananaMatrixEmbedding (perfectBanana P.dimension) (perfectBanana Q.dimension) :=
    ⟨l, r, (by intro a b hab; exact e.left_injective ((hl a).symm.trans
      ((congrArg g.left hab).trans (hl b)))),
     (by intro a b hab; exact e.right_injective ((hr a).symm.trans
      ((congrArg g.right hab).trans (hr b)))),
     by intro x y; rw [← g.pairing_apply, hl, hr, e.pairing_apply]⟩
  refine ⟨⟨carrier, ?_, ?_⟩, hl, hr⟩
  · intro i x
    apply g.left_injective
    change g.left ((Q.actions i).left (l x)) = g.left (l ((P.actions i).left x))
    rw [← hg.1, hl, he.1, hl]
  · intro i y
    apply g.right_injective
    change g.right ((Q.actions i).right (r y)) = g.right (r ((P.actions i).right y))
    rw [← hg.2, hr, he.2, hr]

private structure PerfectBridge {n : ℕ} (s t : BananaNativeTuple n) where
  system : BananaStandardPerfectSystem n
  source : BananaMatrixEmbeddingToLimit (perfectBanana system.dimension)
  target : BananaMatrixEmbeddingToLimit (perfectBanana system.dimension)
  source_realises : BananaPerfectSystemRealises s system source
  target_realises : BananaPerfectSystemRealises t system target

namespace PerfectBridge

variable {n : ℕ} {s t : BananaNativeTuple n}

private def ExtendsBridge (a b : PerfectBridge s t) : Prop :=
  ∃ f : BananaStandardPerfectSystem.Embedding a.system b.system,
    (∀ x, b.source.left (f.carrier.left x) = a.source.left x) ∧
    (∀ y, b.source.right (f.carrier.right y) = a.source.right y) ∧
    (∀ x, b.target.left (f.carrier.left x) = a.target.left x) ∧
    (∀ y, b.target.right (f.carrier.right y) = a.target.right y)

private instance instPreorder : Preorder (PerfectBridge s t) where
  le := ExtendsBridge
  le_refl a := by
    exact ⟨⟨BananaMatrixEmbedding.id _, fun _ _ => rfl, fun _ _ => rfl⟩,
      fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  le_trans a b c hab hbc := by
    obtain ⟨f, hfL, hfR, hfL', hfR'⟩ := hab
    obtain ⟨g, hgL, hgR, hgL', hgR'⟩ := hbc
    have hL i x :=
      (g.intertwines_left i (f.carrier.left x)).trans (congrArg g.carrier.left (f.intertwines_left i x))
    have hR i y :=
      (g.intertwines_right i (f.carrier.right y)).trans (congrArg g.carrier.right (f.intertwines_right i y))
    exact ⟨⟨g.carrier.comp f.carrier, hL, hR⟩,
      fun x => (hgL (f.carrier.left x)).trans (hfL x),
      fun y => (hgR (f.carrier.right y)).trans (hfR y),
      fun x => (hgL' (f.carrier.left x)).trans (hfL' x),
      fun y => (hgR' (f.carrier.right y)).trans (hfR' y)⟩

private def symm (a : PerfectBridge s t) : PerfectBridge t s :=
  ⟨a.system, a.target, a.source, a.target_realises, a.source_realises⟩

private theorem symm_mono {a b : PerfectBridge s t} (h : a ≤ b) : a.symm ≤ b.symm := by
  obtain ⟨f, hL, hR, hL', hR'⟩ := h
  exact ⟨f, hL', hR', hL, hR⟩

private theorem exists_sourceCover (hs : BananaNativeTuple.Covers s) (ht : BananaNativeTuple.Extends t)
    (a : PerfectBridge s t) (L R : Finset BananaLimitVector) :
    ∃ b : PerfectBridge s t, a ≤ b ∧ ↑L ⊆ Set.range b.source.left ∧ ↑R ⊆ Set.range b.source.right := by
  classical
  let L' : Finset BananaLimitVector := Finset.univ.image a.source.left
  let R' : Finset BananaLimitVector := Finset.univ.image a.source.right
  obtain ⟨P, e, he, hL, hR⟩ := hs (L ∪ L') (R ∪ R')
  obtain ⟨f, hfL, hfR⟩ := realisesFactor a.source_realises he
    (fun x ⟨z, hz⟩ => hL (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, hz⟩)))
    (fun y ⟨z, hz⟩ => hR (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, Finset.mem_univ _, hz⟩)))
  obtain ⟨g, hg, hgL, hgR⟩ := ht _ _ f a.target a.target_realises
  let b : PerfectBridge s t := ⟨P, e, g, he, hg⟩
  exact ⟨b, ⟨f, hfL, hfR, hgL, hgR⟩,
    fun x hx => hL (Finset.mem_union_left _ hx),
    fun y hy => hR (Finset.mem_union_left _ hy)⟩

private abbrev TaggedPoint := BananaLimitVector ⊕ BananaLimitVector

private def sourceContains (a : PerfectBridge s t) : TaggedPoint → Prop
  | .inl x => x ∈ Set.range a.source.left
  | .inr y => y ∈ Set.range a.source.right

private def sourceCofinal (hs : BananaNativeTuple.Covers s) (ht : BananaNativeTuple.Extends t) (x : TaggedPoint) :
    Order.Cofinal (PerfectBridge s t) where
  carrier := {b | b.sourceContains x}
  isCofinal := by
    intro a
    cases x with
    | inl x =>
      obtain ⟨b, hab, hx, _⟩ := exists_sourceCover hs ht a {x} ∅
      exact ⟨b, hx (Finset.mem_singleton_self _), hab⟩
    | inr y =>
      obtain ⟨b, hab, _, hy⟩ := exists_sourceCover hs ht a ∅ {y}
      exact ⟨b, hy (Finset.mem_singleton_self _), hab⟩

private def targetCofinal (ht : BananaNativeTuple.Covers t) (hs : BananaNativeTuple.Extends s) (x : TaggedPoint) :
    Order.Cofinal (PerfectBridge s t) where
  carrier := {b | b.symm.sourceContains x}
  isCofinal := by
    intro a
    obtain ⟨b, hb, hab⟩ := (sourceCofinal ht hs x).isCofinal a.symm
    exact ⟨b.symm, hb, symm_mono hab⟩

private noncomputable def zeroBridge (s t : BananaNativeTuple n) : PerfectBridge s t := by
  let P : BananaStandardPerfectSystem n := ⟨0, fun _ => BananaMatrixEmbedding.id _⟩
  let e : BananaMatrixEmbeddingToLimit (perfectBanana P.dimension) :=
    bananaLimitBlockStandardEmbedding (∅ : Finset ℚ)
  have h (v : BananaNativeTuple n) : BananaPerfectSystemRealises v P e := by
    constructor
    · intro i x
      rw [Subsingleton.elim x 0]
      change (v i).val.1 (e.left 0) = e.left 0
      simp only [map_zero]
    · intro i y
      rw [Subsingleton.elim y 0]
      change (v i).val.2 (e.right 0) = e.right 0
      simp only [map_zero]
  exact ⟨P, e, e, h s, h t⟩

end PerfectBridge

private theorem exists_linearEquiv_of_coherent_ranges
    {U : ℕ → Type} [∀ k, AddCommGroup (U k)] [∀ k, Module F2 (U k)]
    (f g : ∀ k, U k →ₗ[F2] BananaLimitVector)
    (hf : ∀ k, Function.Injective (f k)) (hg : ∀ k, Function.Injective (g k))
    (hstep : ∀ i j, i ≤ j → ∀ x : U i, ∃ y : U j, f j y = f i x ∧ g j y = g i x)
    (hsource : ∀ x, ∃ k, x ∈ Set.range (f k))
    (htarget : ∀ y, ∃ k, y ∈ Set.range (g k)) :
    ∃ E : BananaLimitVector ≃ₗ[F2] BananaLimitVector, ∀ k x, E (f k x) = g k x := by
  classical
  let graph (x y : BananaLimitVector) := ∃ k, ∃ z : U k, f k z = x ∧ g k z = y
  have common {i j : ℕ} (x : U i) (y : U j) :
      ∃ a b : U (max i j), f _ a = f _ x ∧ g _ a = g _ x ∧
        f _ b = f _ y ∧ g _ b = g _ y := by
    obtain ⟨a, ha₁, ha₂⟩ := hstep i (max i j) (le_max_left i j) x
    obtain ⟨b, hb₁, hb₂⟩ := hstep j (max i j) (le_max_right i j) y
    exact ⟨a, b, ha₁, ha₂, hb₁, hb₂⟩
  have rightUnique {x y y'} (h₁ : graph x y) (h₂ : graph x y') : y = y' := by
    obtain ⟨i, a, ha₁, ha₂⟩ := h₁
    obtain ⟨j, b, hb₁, hb₂⟩ := h₂
    obtain ⟨a', b', hfa, hga, hfb, hgb⟩ := common a b
    have heq : a' = b' := hf _ ((hfa.trans ha₁).trans (hfb.trans hb₁).symm)
    exact (hga.trans ha₂).symm.trans ((congrArg (g _) heq).trans (hgb.trans hb₂))
  have leftUnique {x x' y} (h₁ : graph x y) (h₂ : graph x' y) : x = x' := by
    obtain ⟨i, a, ha₁, ha₂⟩ := h₁
    obtain ⟨j, b, hb₁, hb₂⟩ := h₂
    obtain ⟨a', b', hfa, hga, hfb, hgb⟩ := common a b
    have heq : a' = b' := hg _ ((hga.trans ha₂).trans (hgb.trans hb₂).symm)
    exact (hfa.trans ha₁).symm.trans ((congrArg (f _) heq).trans (hfb.trans hb₁))
  have htotal (x : BananaLimitVector) : ∃ y, graph x y := by
    obtain ⟨i, z, hz⟩ := hsource x
    exact ⟨g i z, i, z, hz, rfl⟩
  let F (x : BananaLimitVector) := (htotal x).choose
  have hF (x : BananaLimitVector) : graph x (F x) := (htotal x).choose_spec
  have hF' (k : ℕ) (z : U k) : F (f k z) = g k z :=
    rightUnique (hF _) ⟨k, z, rfl, rfl⟩
  let Fₗ : BananaLimitVector →ₗ[F2] BananaLimitVector := {
    toFun := F
    map_add' x y := by
      obtain ⟨i, a, rfl⟩ := hsource x
      obtain ⟨j, b, rfl⟩ := hsource y
      obtain ⟨a', b', hfa, hga, hfb, hgb⟩ := common a b
      rw [← hfa, ← hfb, ← map_add, hF', map_add, hF', hF']
    map_smul' r x := by
      obtain ⟨i, a, rfl⟩ := hsource x
      change F (r • f i a) = r • F (f i a)
      rw [← map_smul, hF', hF', map_smul] }
  have hbij : Function.Bijective Fₗ := by
    constructor
    · intro x x' h
      change F x = F x' at h
      exact leftUnique (hF x) (show graph x' (F x) from h.symm ▸ hF x')
    · intro y
      obtain ⟨i, z, rfl⟩ := htarget y
      exact ⟨f i z, hF' i z⟩
  exact ⟨LinearEquiv.ofBijective Fₗ hbij, hF'⟩

/-- Two tuples with cofinal perfect systems and the perfect-system extension
property are simultaneously conjugate in the native automorphism group. -/
theorem bananaLimit_exists_diagonalConjugator_of_perfectSystemExtension
    {n : ℕ} (s t : Fin n → BananaLimitAutomorphism)
    (hs : BananaNativeTuple.Covers s) (ht : BananaNativeTuple.Covers t) (hse : BananaNativeTuple.Extends s) (hte : BananaNativeTuple.Extends t) :
    ∃ g : ConjAct BananaLimitAutomorphism, g • s = t := by
  classical
  let := Encodable.ofCountable (PerfectBridge.TaggedPoint ⊕ PerfectBridge.TaggedPoint)
  let D : PerfectBridge.TaggedPoint ⊕ PerfectBridge.TaggedPoint → Order.Cofinal (PerfectBridge s t)
    := Sum.elim (PerfectBridge.sourceCofinal hs hte) (PerfectBridge.targetCofinal ht hse)
  let first := PerfectBridge.zeroBridge s t
  let B := Order.sequenceOfCofinals first D
  have hmono : Monotone B := Order.sequenceOfCofinals.monotone first D
  have hcover (a : PerfectBridge.TaggedPoint ⊕ PerfectBridge.TaggedPoint) :
      B (Encodable.encode a + 1) ∈ D a := Order.sequenceOfCofinals.encode_mem first D a
  have hSL (x : BananaLimitVector) : ∃ k, x ∈ Set.range (B k).source.left :=
    ⟨_, hcover (.inl (.inl x))⟩
  have hSR (x : BananaLimitVector) : ∃ k, x ∈ Set.range (B k).source.right :=
    ⟨_, hcover (.inl (.inr x))⟩
  have hTL (x : BananaLimitVector) : ∃ k, x ∈ Set.range (B k).target.left :=
    ⟨_, hcover (.inr (.inl x))⟩
  have hTR (x : BananaLimitVector) : ∃ k, x ∈ Set.range (B k).target.right :=
    ⟨_, hcover (.inr (.inr x))⟩
  obtain ⟨L, hL⟩ := exists_linearEquiv_of_coherent_ranges
    (fun k => (B k).source.left) (fun k => (B k).target.left)
    (fun k => (B k).source.left_injective) (fun k => (B k).target.left_injective)
    (fun i j hij x => by
      obtain ⟨f, h₁, _, h₂, _⟩ := hmono hij
      exact ⟨f.carrier.left x, h₁ x, h₂ x⟩) hSL hTL
  obtain ⟨R, hR⟩ := exists_linearEquiv_of_coherent_ranges
    (fun k => (B k).source.right) (fun k => (B k).target.right)
    (fun k => (B k).source.right_injective) (fun k => (B k).target.right_injective)
    (fun i j hij y => by
      obtain ⟨f, _, h₁, _, h₂⟩ := hmono hij
      exact ⟨f.carrier.right y, h₁ y, h₂ y⟩) hSR hTR
  have hpair (x y : BananaLimitVector) :
      bananaLimitPairing (L x) (R y) = bananaLimitPairing x y := by
    obtain ⟨i, a, ha⟩ := hSL x
    obtain ⟨j, b, hb⟩ := hSR y
    let k := max i j
    obtain ⟨fa, hfa, _, _, _⟩ := hmono (show i ≤ k from le_max_left i j)
    obtain ⟨fb, _, hfb, _, _⟩ := hmono (show j ≤ k from le_max_right i j)
    have hx := (hfa a).trans ha
    have hy := (hfb b).trans hb
    rw [← hx, ← hy, hL, hR, (B k).target.pairing_apply, (B k).source.pairing_apply]
  let g : BananaLimitAutomorphism := ⟨(L, R), hpair⟩
  refine ⟨ConjAct.toConjAct g, ?_⟩
  funext i
  change g * s i * g⁻¹ = t i
  apply (mul_inv_eq_iff_eq_mul).2
  apply Subtype.ext
  apply Prod.ext
  · apply LinearEquiv.ext
    intro x
    change L ((s i).val.1 x) = (t i).val.1 (L x)
    obtain ⟨k, z, rfl⟩ := hSL x
    rw [(B k).source_realises.1, hL, hL, (B k).target_realises.1]
  · apply LinearEquiv.ext
    intro y
    change R ((s i).val.2 y) = (t i).val.2 (R y)
    obtain ⟨k, z, rfl⟩ := hSR y
    rw [(B k).source_realises.2, hR, hR, (B k).target_realises.2]


/-- The rich tuples lie in one orbit, and the rich set is comeagre.
Consequently simultaneous conjugation has a comeagre orbit in each
finite power of the native BANANA automorphism group. -/
theorem bananaLimit_exists_comeagre_diagonalConjugacyOrbit (n : ℕ) :
    ∃ t : BananaNativeTuple n,
      MulAction.orbit (ConjAct BananaLimitAutomorphism) t ∈ residual _ := by
  let := bananaLimitAutomorphism_polishSpace
  have hr := BananaNativeTuple.rich_mem_residual n
  obtain ⟨s, hs⟩ := (dense_of_mem_residual hr).nonempty
  refine ⟨s, mem_of_superset hr ?_⟩
  intro t ht
  exact bananaLimit_exists_diagonalConjugator_of_perfectSystemExtension s t
    hs.1 ht.1 hs.2 ht.2

end SuccessorTree.NonPrecompact
