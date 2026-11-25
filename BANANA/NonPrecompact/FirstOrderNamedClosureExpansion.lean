import BANANA.NonPrecompact.FiniteSetClosureFamily
import BANANA.NonPrecompact.FirstOrderExpansionRestriction
import Mathlib.ModelTheory.Fraisse
import Mathlib.Data.Fintype.Sets
import Mathlib.Basic.Finite.Sigma

/-!
# Expanding a chosen family of finite substructures

A cofinal, intersection-closed family of finite reduct substructures can
be made exactly the finite closed substructures of an expansion. Naming
points by predicates makes all embeddings in the expanded age unique.
If the family has finite cardinality fibres, so does the expanded age.
-/

namespace SuccessorTree.NonPrecompact

open CategoryTheory FirstOrder Function
open scoped FirstOrder
open Language.Structure Language.Substructure

universe u v w

/-- A cofinal family of finite reduct substructures, closed under binary
intersection. The reduct need not have a constant. -/
structure FiniteClosureFamily (L : Language.{u, v}) (M : Type w) [L.Structure M]
    [DecidableEq M] extends FiniteSetClosureFamily M where
  fun_mem : ∀ ⦃s⦄, s ∈ members → ∀ {n} (f : L.Functions n) (x : Fin n → M),
    (∀ i, x i ∈ s) → funMap f x ∈ s

namespace FiniteClosureFamily

variable {L : Language.{u,v}} {M : Type w} [L.Structure M] [DecidableEq M]
variable (F : FiniteClosureFamily L M)

/-- A positive-arity function for each point, a constant for each point
in the least selected set, and a unary predicate for each point. -/
noncomputable def addedLanguage : Language.{w,w} where
  Functions n := (PLift (n = 0) × ↥(F.toFiniteSetClosureFamily.envelope ∅)) ⊕ (PLift (0 < n) × M)
  Relations n := PLift (n = 1) × M

noncomputable abbrev expandedLanguage : Language := L.sum F.addedLanguage

instance countable_expandedSymbols [Countable M] [Countable L.Symbols] :
    Countable F.expandedLanguage.Symbols := by
  have hFunction (n : ℕ) : Countable (L.Functions n) :=
    Injective.countable (f := fun f => (Sum.inl ⟨n, f⟩ : L.Symbols))
      (Sum.inl_injective.comp sigma_mk_injective)
  have hRelation (n : ℕ) : Countable (L.Relations n) :=
    Injective.countable (f := fun r => (Sum.inr ⟨n, r⟩ : L.Symbols))
      (Sum.inr_injective.comp sigma_mk_injective)
  have hAddedFunction (n : ℕ) : Countable (F.addedLanguage.Functions n) := by
    change Countable ((PLift (n = 0) × ↥(F.toFiniteSetClosureFamily.envelope ∅)) ⊕
      (PLift (0 < n) × M))
    infer_instance
  have hAddedRelation (n : ℕ) : Countable (F.addedLanguage.Relations n) := by
    change Countable (PLift (n = 1) × M)
    infer_instance
  change Countable ((Σ n, L.Functions n ⊕ F.addedLanguage.Functions n) ⊕
    (Σ n, L.Relations n ⊕ F.addedLanguage.Relations n))
  infer_instance

noncomputable instance addedStructure : F.addedLanguage.Structure M where
  funMap f x := match f with
    | Sum.inl p => p.2
    | Sum.inr p =>
      if p.2 ∈ F.toFiniteSetClosureFamily.envelope (Finset.univ.image x) then p.2
      else x ⟨0, p.1.down⟩
  RelMap r x := x ⟨0, r.1.down.symm ▸ Nat.zero_lt_one⟩ = r.2

noncomputable instance expandedStructure : F.expandedLanguage.Structure M :=
  Language.sumStructure L F.addedLanguage M

noncomputable def inclusion : L →ᴸ F.expandedLanguage := Language.LHom.sumInl

instance expansionOn : F.inclusion.IsExpansionOn M where
  map_onFunction _ _ := rfl
  map_onRelation _ _ := rfl

/-- Forget only the added functions and predicates, keeping the same set. -/
noncomputable abbrev reductSubstructure (S : F.expandedLanguage.Substructure M) : L.Substructure M :=
  F.inclusion.substructureReduct S

/-- A selected set carries the induced expanded substructure. -/
noncomputable def substructure (s : Finset M) (hs : s ∈ F.members) :
    F.expandedLanguage.Substructure M where
  carrier := s
  fun_mem := by
    intro n f x hx
    rcases f with f | (p | p)
    · exact F.fun_mem hs f x hx
    · exact F.toFiniteSetClosureFamily.envelope_subset hs (Finset.empty_subset s) p.2.property
    · change (if p.2 ∈ F.toFiniteSetClosureFamily.envelope (Finset.univ.image x) then p.2 else x ⟨0, p.1.down⟩) ∈ s
      split
      · rename_i hp
        apply F.toFiniteSetClosureFamily.envelope_subset hs _ hp
        intro y hy
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
        exact hx i
      · exact hx _

@[simp] theorem coe_substructure (s : Finset M) (hs : s ∈ F.members) :
    (F.substructure s hs : Set M) = (s : Set M) := rfl

/-- Closing any tuple in an expanded substructure includes its entire
selected hull. -/
theorem hull_image_subset {n : ℕ} (S : F.expandedLanguage.Substructure M)
    (x : Fin n → M) (hx : ∀ i, x i ∈ S) :
    (F.toFiniteSetClosureFamily.envelope (Finset.univ.image x) : Set M) ⊆ S := by
  intro p hp
  by_cases hn : n = 0
  · subst n
    have he : Finset.univ.image x = ∅ := Finset.eq_empty_of_forall_notMem fun y hy =>
      let ⟨i, _, _⟩ := Finset.mem_image.mp hy
      Fin.elim0 i
    rw [he] at hp
    let f : F.addedLanguage.Functions 0 := Sum.inl ⟨⟨rfl⟩, ⟨p, hp⟩⟩
    exact S.fun_mem (Sum.inr f) x hx
  · let f : F.addedLanguage.Functions n := Sum.inr ⟨⟨Nat.pos_of_ne_zero hn⟩, p⟩
    have h := S.fun_mem (Sum.inr f) x hx
    change (if p ∈ F.toFiniteSetClosureFamily.envelope (Finset.univ.image x) then p else x ⟨0, Nat.pos_of_ne_zero hn⟩) ∈ S at h
    have hp' : p ∈ F.toFiniteSetClosureFamily.envelope (Finset.univ.image x) := hp
    rw [ite_eq_left hp'] at h
    exact h

/-- Any finite subset of an expanded substructure is contained in a
selected member of the same substructure. -/
theorem hull_subset_substructure (S : F.expandedLanguage.Substructure M)
    {s : Finset M} (hs : (s : Set M) ⊆ S) :
    (F.toFiniteSetClosureFamily.envelope s : Set M) ⊆ S := by
  classical
  let e : Fin (Fintype.card ↥s) ≃ ↥s := (Fintype.equivFin ↥s).symm
  let x := fun i => (e i).val
  have he : Finset.univ.image x = s := by
    ext p
    rw [Finset.mem_image]
    constructor
    · rintro ⟨i, _, rfl⟩
      exact (e i).property
    · intro hp
      exact ⟨e.symm ⟨p,hp⟩, Finset.mem_univ _, congrArg Subtype.val (e.apply_symm_apply _)⟩
  rw [← he]
  exact F.hull_image_subset S x (fun i => hs (e i).property)

/-- Expanded finitely generated substructures are finite. -/
theorem fg_finite {S : F.expandedLanguage.Substructure M} (h : S.FG) : Finite S := by
  obtain ⟨s, rfl⟩ := h
  have hs : (s : Set M) ⊆ F.toFiniteSetClosureFamily.envelope s := F.toFiniteSetClosureFamily.subset_envelope s
  let R := F.substructure (F.toFiniteSetClosureFamily.envelope s) (F.toFiniteSetClosureFamily.envelope_mem s)
  have hle : closure F.expandedLanguage (s : Set M) ≤ R := closure_le.mpr hs
  let : Finite R := Finite.of_fintype ↥(F.toFiniteSetClosureFamily.envelope s)
  exact Finite.of_injective (Set.inclusion hle) (Set.inclusion_injective hle)

/-- The finite substructures of the expansion are exactly the selected sets. -/
theorem finite_substructure_iff (S : F.expandedLanguage.Substructure M) :
    Finite S ↔ ∃ (s : Finset M) (hs : s ∈ F.members), (F.substructure s hs) = S := by
  constructor
  · intro h
    have hset : (S : Set M).Finite := Set.toFinite _
    let s := hset.toFinset
    have hcoe : (s : Set M) = S := hset.coe_toFinset
    have hEq : (F.toFiniteSetClosureFamily.envelope s : Set M) = S := by
      apply le_antisymm (F.hull_subset_substructure S hcoe.le)
      rw [← hcoe]
      exact F.toFiniteSetClosureFamily.subset_envelope s
    exact ⟨F.toFiniteSetClosureFamily.envelope s, F.toFiniteSetClosureFamily.envelope_mem s, SetLike.coe_injective hEq⟩
  · rintro ⟨s, hs, rfl⟩
    exact Finite.of_fintype ↥s

/-- In the expansion every point is identified by its singleton predicate. -/
theorem embedding_eq_subtype (S : F.expandedLanguage.Substructure M)
    (e : S ↪[F.expandedLanguage] M) : e = S.subtype := by
  ext x
  let r : F.addedLanguage.Relations 1  := (⟨rfl⟩, (x : M))
  have h := e.map_rel (Sum.inr r) (fun _ => x)
  change (e x = (x : M)) ↔ (x : M) = x at h
  exact h.mpr rfl

theorem ultrahomogeneous : F.expandedLanguage.IsUltrahomogeneous M := by
  intro S _ e
  exact ⟨Language.Equiv.refl _ _, (F.embedding_eq_subtype S e).trans
    (Language.Embedding.refl_comp _).symm⟩

/-- Each finite member of the expanded age has only one image in the
ambient expansion. -/
theorem age_embedding_subsingleton {A : Type w} [F.expandedLanguage.Structure A]
    (e g : A ↪[F.expandedLanguage] M) : e = g := by
  ext x
  let r : F.addedLanguage.Relations 1  := (⟨rfl⟩, e x)
  have he := e.map_rel (Sum.inr r) (fun _ => x)
  have hg := g.map_rel (Sum.inr r) (fun _ => x)
  have h : RelMap (L := F.expandedLanguage) (Sum.inr r) (fun _ => x) := he.mp rfl
  exact (hg.mpr h).symm

/-- Expanded embeddings are unique whenever the target embeds in the
ambient expansion. -/
theorem embedding_subsingleton_of_target {A B : Type w}
    [F.expandedLanguage.Structure A] [F.expandedLanguage.Structure B]
    (b : B ↪[F.expandedLanguage] M) (e g : A ↪[F.expandedLanguage] B) : e = g :=
  b.comp_injective (F.age_embedding_subsingleton (b.comp e) (b.comp g))

/-- The age of the expansion is a Fraïssé class on a countable carrier. -/
theorem age_isFraisse [Countable M] :
    Language.IsFraisse (F.expandedLanguage.age M) :=
  F.ultrahomogeneous.age_isFraisse

/-- The countable expansion is itself the Fraïssé limit of this age. -/
theorem isFraisseLimit_age [Countable M] [Countable L.Symbols] :
    Language.IsFraisseLimit (F.expandedLanguage.age M) M :=
  ⟨F.ultrahomogeneous, rfl⟩

/-- Every member of the expanded age has a finite carrier. -/
theorem finite_of_mem_age {A : Bundled.{w} F.expandedLanguage.Structure}
    (hA : A ∈ F.expandedLanguage.age M) : Finite A := by
  let e := hA.2.some
  have h := F.fg_finite (hA.1.range e.toHom)
  exact Finite.of_injective e.equivRange e.equivRange.injective

/-- An embedding of a finite expanded structure has selected range. -/
theorem exists_selected_range {A : Type w} [F.expandedLanguage.Structure A] [Finite A]
    (e : A ↪[F.expandedLanguage] M) :
    ∃ s ∈ F.members, (s : Set M) = Set.range e := by
  let : Finite e.toHom.range := Finite.of_surjective e.equivRange e.equivRange.surjective
  obtain ⟨s, hs, h⟩ := (F.finite_substructure_iff e.toHom.range).mp inferInstance
  exact ⟨s, hs, congrArg (fun S : F.expandedLanguage.Substructure M => (S : Set M)) h⟩

/-- Every finite reduct carrier admits only finitely many labelled interpretations
that embed in this expansion. This is stronger than finiteness up to isomorphism. -/
theorem finite_labelledStructures {A : Type w} [Finite A]
    (hF : ∀ n, {s ∈ F.members | s.card = n}.Finite) :
    {T : F.expandedLanguage.Structure A |
      Nonempty (@Language.Embedding F.expandedLanguage A M T _)}.Finite := by
  classical
  let := Fintype.ofFinite A
  let X : Set (F.expandedLanguage.Structure A) :=
    {T | Nonempty (@Language.Embedding F.expandedLanguage A M T _)}
  let Y : Set (Finset M) := {s ∈ F.members | s.card = Fintype.card A}
  let getEmbedding (T : X) : @Language.Embedding F.expandedLanguage A M T.val _ := T.property.some
  have getSelected (T : X) : ∃ s ∈ Y, (s : Set M) = Set.range (getEmbedding T) := by
    let : F.expandedLanguage.Structure A := T.val
    let e := getEmbedding T
    obtain ⟨s, hs, h⟩ := F.exists_selected_range e
    have he : (e.toHom.range : Set M) = (s : Set M) := h.symm
    have hc' := Fintype.card_congr (e.equivRange.toEquiv.trans (Set.equivOfEq he))
    exact ⟨s, ⟨hs, (Fintype.card_coe s).symm.trans hc'.symm⟩, h⟩
  let getFinset (T : X) : Y := ⟨(getSelected T).choose, (getSelected T).choose_spec.1⟩
  let pack (T : X) : Σ s : Y, A → ↥s.val :=
    ⟨getFinset T, fun x => ⟨getEmbedding T x, by
      have h := (getSelected T).choose_spec.2
      change getEmbedding T x ∈ ((getSelected T).choose : Set M)
      rw [h]
      exact Set.mem_range_self x⟩⟩
  have hpack : Injective pack := by
    intro T U hu
    apply Subtype.ext
    apply firstOrderExpansion_eq_of_embeddings (getEmbedding T) (getEmbedding U)
    intro x
    let unpack (p : Σ s : Y, A → ↥s.val) : M := (p.2 x).val
    exact congrArg unpack hu
  let : Finite Y := hF _
  have (s : Y) : Finite (A → ↥s.val) := Finite.of_fintype _
  exact Finite.of_injective pack hpack

/-- The actual finite age has the embedding Ramsey property, since there is
at most one source embedding into the prescribed target. -/
theorem age_embeddingRamsey (A B : Bundled.{w} F.expandedLanguage.Structure)
    (hB : B ∈ F.expandedLanguage.age M) (r : ℕ) :
    ∃ C ∈ F.expandedLanguage.age M,
      ∀ c : (A ↪[F.expandedLanguage] C) → Fin r,
        ∃ b : B ↪[F.expandedLanguage] C,
          ∀ f g : A ↪[F.expandedLanguage] B, c (b.comp f) = c (b.comp g) := by
  refine ⟨B, hB, fun c => ⟨Language.Embedding.refl _ _, fun f g => ?_⟩⟩
  rw [F.embedding_subsingleton_of_target hB.2.some f g]

/-- Finite reduct embeddings that already have selected range can be regarded as
embeddings in the expanded age with the original reduct. -/
theorem rangeClosed_of_selected_range {A : Type w} [L.Structure A]
    (a : A ↪[L] M) (ha : ∃ s ∈ F.members, (s : Set M) = Set.range a) :
    ExpandedRangeClosed (L' := F.expandedLanguage) a := by
  obtain ⟨s, hs, he⟩ := ha
  exact (expandedRangeClosed_iff_exists_substructure a).mpr ⟨F.substructure s hs, he⟩

/-- The same embedding on the reducts of an expanded source and target. -/
def reductEmbedding {A : Type w} [L.Structure A] [F.expandedLanguage.Structure A]
    [F.inclusion.IsExpansionOn A] (a : A ↪[F.expandedLanguage] M) : A ↪[L] M where
  toEmbedding := a.toEmbedding
  map_fun' f x := by
    change a (funMap f x) = funMap f (a ∘ x)
    simpa only [F.inclusion.map_onFunction] using a.map_fun (F.inclusion.onFunction f) x
  map_rel' R x := by
    change RelMap R (a ∘ x) ↔ RelMap R x
    simpa only [F.inclusion.map_onRelation] using a.map_rel (F.inclusion.onRelation R) x

private theorem exists_lift_of_commuting {A B : Type w} [L.Structure A] [L.Structure B]
    [SA : F.expandedLanguage.Structure A] (a : A ↪[F.expandedLanguage] M)
    (e : A ↪[L] B) (b : B ↪[L] M) (h : ∀ x, b (e x) = a x)
    (hb : ExpandedRangeClosed (L' := F.expandedLanguage) b) :
    ∃ g : @Language.Embedding F.expandedLanguage A B SA (restrictFirstOrderExpansion b hb),
      ∀ x, @Language.Embedding.toEmbedding _ _ _ SA (restrictFirstOrderExpansion b hb) g x = e x := by
  let EB := restrictFirstOrderExpansion b hb
  let _ : F.expandedLanguage.Structure B := EB
  let b' : B ↪[F.expandedLanguage] M := restrictFirstOrderExpansion_embedding b hb
  have h' : ∀ x, b' (e x) = a x := h
  have htuple {n : ℕ} (x : Fin n → A) :
      (b' : B → M) ∘ (e : A → B) ∘ x = a ∘ x := funext fun i => h' (x i)
  let g : A ↪[F.expandedLanguage] B := {
    toEmbedding := e.toEmbedding
    map_fun' := by
      intro n f x
      apply b'.injective
      change b' (e (funMap f x)) = b' (funMap f (e ∘ x))
      rw [h', b'.map_fun, htuple, a.map_fun]
    map_rel' := by
      intro n R x
      change RelMap R ((e : A → B) ∘ x) ↔ RelMap R x
      rw [← b'.map_rel, htuple, a.map_rel] }
  exact ⟨g, fun _ => rfl⟩

/-- The selected extension property implies reasonableness for every
prescribed expansion of the source belonging to the actual finite age. -/
theorem exists_expansion_lift {A B : Type w} [L.Structure A] [L.Structure B]
    [Finite A] [SA : F.expandedLanguage.Structure A] [F.inclusion.IsExpansionOn A]
    (a : A ↪[F.expandedLanguage] M) (e : A ↪[L] B)
    (hLift : ∀ a₀ : A ↪[L] M, (∃ s ∈ F.members, (s : Set M) = Set.range a₀) →
      ∃ b : B ↪[L] M, (∀ x, b (e x) = a₀ x) ∧
        ∃ s ∈ F.members, (s : Set M) = Set.range b) :
    ∃ (SB : F.expandedLanguage.Structure B) (_ : @Language.LHom.IsExpansionOn _ _
        F.inclusion B _ SB) (b : @Language.Embedding F.expandedLanguage B M SB _)
      (g : @Language.Embedding F.expandedLanguage A B SA SB),
        (∀ x, @Language.Embedding.toEmbedding _ _ _ SA SB g x = e x) ∧
          ∀ x, @Language.Embedding.toEmbedding _ _ _ SB _ b
            (@Language.Embedding.toEmbedding _ _ _ SA SB g x) = a x := by
  obtain ⟨b, hb, hs⟩ := hLift (F.reductEmbedding a) (F.exists_selected_range a)
  let hc := F.rangeClosed_of_selected_range b hs
  obtain ⟨g, hg⟩ := F.exists_lift_of_commuting a e b hb hc
  exact ⟨restrictFirstOrderExpansion b hc, restrictFirstOrderExpansion_isExpansionOn F.inclusion b hc,
    restrictFirstOrderExpansion_embedding b hc, g, hg, fun x => by
      change b (@Language.Embedding.toEmbedding _ _ _ SA (restrictFirstOrderExpansion b hc) g x) = a x
      rw [hg]
      exact hb x⟩

/-- Age coverage follows from a reduct embedding with selected range. -/
theorem exists_expandedStructure_of_selected_range {B : Type w} [L.Structure B]
    (b : B ↪[L] M) (hb : ∃ s ∈ F.members, (s : Set M) = Set.range b) :
    ∃ (SB : F.expandedLanguage.Structure B) (_ : @Language.LHom.IsExpansionOn _ _
        F.inclusion B _ SB), Nonempty (@Language.Embedding F.expandedLanguage B M SB _) := by
  let hc := F.rangeClosed_of_selected_range b hb
  exact ⟨restrictFirstOrderExpansion b hc, restrictFirstOrderExpansion_isExpansionOn F.inclusion b hc,
    ⟨restrictFirstOrderExpansion_embedding b hc⟩⟩

end FiniteClosureFamily

end SuccessorTree.NonPrecompact
