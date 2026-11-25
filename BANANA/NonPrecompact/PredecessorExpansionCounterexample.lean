import Mathlib.ModelTheory.Substructures
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.ByContra

/-!
# A unary function can invalidate the degree bound for expansions

Take a unary-marked set with two marked points and infinitely many
unmarked points. Expand it by the predecessor function on each of the
two enumerations, fixing the first point. The finite closed subsets
are exactly pairs of prefixes. One marked point has only one possible
expansion, although the two marked points can be coloured differently.
-/

namespace SuccessorTree.NonPrecompact.PredecessorExpansion

open FirstOrder Function
open scoped FirstOrder

/-- The unary predicate distinguishes the two marked points. -/
inductive MarkSymbol : ℕ → Type
  | mark : MarkSymbol 1

/-- There is one added unary function, interpreted as predecessor. -/
inductive PredSymbol : ℕ → Type
  | pred : PredSymbol 1

def reductLanguage : Language where
  Functions _ := Empty
  Relations := MarkSymbol

def expandedLanguage : Language where
  Functions := PredSymbol
  Relations := MarkSymbol

/-- Finite reducts have at most two marked points. -/
structure Profile where
  marked : ℕ
  unmarked : ℕ
  marked_le : marked ≤ 2

abbrev Points (A : Profile) := Fin A.marked ⊕ Fin A.unmarked

def marked {X Y : Type*} : X ⊕ Y → Prop
  | .inl _ => True
  | .inr _ => False

def finPred {n : ℕ} (i : Fin n) : Fin n :=
  ⟨i.val - 1, (Nat.sub_le _ _).trans_lt i.isLt⟩

@[instance_reducible] def reductStructure (X Y : Type*) : reductLanguage.Structure (X ⊕ Y) where
  funMap f := Empty.elim f
  RelMap r a := match r with
    | .mark => marked (a 0)

@[instance_reducible] def expandedStructure {X Y : Type*} (left : X → X) (right : Y → Y) :
    expandedLanguage.Structure (X ⊕ Y) where
  funMap f a := match f with
    | .pred => Sum.map left right (a 0)
  RelMap r a := match r with
    | .mark => marked (a 0)

instance profileReductStructure (A : Profile) : reductLanguage.Structure (Points A) :=
  reductStructure _ _

instance profileExpandedStructure (A : Profile) : expandedLanguage.Structure (Points A) :=
  expandedStructure finPred finPred

abbrev Limit := Fin 2 ⊕ ℕ

instance : reductLanguage.Structure Limit := reductStructure _ _
instance : expandedLanguage.Structure Limit := expandedStructure finPred Nat.pred

/-- The reduct literally forgets the added predecessor symbol. -/
def inclusion : reductLanguage →ᴸ expandedLanguage where
  onFunction {_} f := Empty.elim f
  onRelation {_} r := r

instance (A : Profile) : inclusion.IsExpansionOn (Points A) where
  map_onFunction {_} f := Empty.elim f
  map_onRelation _ _ := rfl

instance : inclusion.IsExpansionOn Limit where
  map_onFunction {_} f := Empty.elim f
  map_onRelation _ _ := rfl

/-- The coordinate embeddings of the two prefixes into the infinite expansion. -/
def embedLimit (A : Profile) : Points A ↪[expandedLanguage] Limit where
  toEmbedding := (Fin.castLEEmb A.marked_le).sumMap ⟨Fin.val, Fin.val_injective⟩
  map_fun' f a := by
    cases f
    change Sum.map (Fin.castLE A.marked_le) Fin.val (Sum.map finPred finPred (a 0)) =
      Sum.map finPred Nat.pred (Sum.map (Fin.castLE A.marked_le) Fin.val (a 0))
    cases a 0 <;> rfl
  map_rel' r a := by
    cases r
    change marked (Sum.map (Fin.castLE A.marked_le) Fin.val (a 0)) ↔ marked (a 0)
    cases a 0 <;> rfl

private theorem rank_eq_of_preserves_pred {m : ℕ} (f : Fin m → ℕ) (hf : Injective f)
    (commutes : ∀ i, f (finPred i) = f i - 1) (i : Fin m) : f i = i.val := by
  induction h : i.val using Nat.strong_induction_on generalizing i with
  | h n ih =>
    by_cases hz : n = 0
    · have hi : finPred i = i := Fin.ext (by simp [finPred, h, hz])
      have eq := commutes i
      rw [hi] at eq
      omega
    · have hlt : (finPred i).val < n := by simp [finPred, h]; omega
      have hprev := ih (finPred i).val hlt (finPred i) rfl
      have heq := commutes i
      have hne : f (finPred i) ≠ f i := fun he => by
        have hval := congrArg Fin.val (hf he)
        change i.val - 1 = i.val at hval
        omega
      change f (finPred i) = i.val - 1 at hprev
      omega

variable {A B C : Profile}

/-- The reduct embeddings of the two sorts may be arbitrary injections. -/
def embedReduct (l : Fin A.marked ↪ Fin B.marked) (r : Fin A.unmarked ↪ Fin B.unmarked) :
    Points A ↪[reductLanguage] Points B where
  toEmbedding := l.sumMap r
  map_fun' f := Empty.elim f
  map_rel' f a := by
    cases f
    change marked ((l.sumMap r) (a 0)) ↔ marked (a 0)
    cases a 0 <;> rfl

/-- The unique expanded embedding between nested prefixes. -/
def embedExpanded (hl : A.marked ≤ B.marked) (hr : A.unmarked ≤ B.unmarked) :
    Points A ↪[expandedLanguage] Points B where
  toEmbedding := (Fin.castLEEmb hl).sumMap (Fin.castLEEmb hr)
  map_fun' f a := by
    cases f
    change Sum.map (Fin.castLE hl) (Fin.castLE hr) (Sum.map finPred finPred (a 0)) =
      Sum.map finPred finPred (Sum.map (Fin.castLE hl) (Fin.castLE hr) (a 0))
    cases a 0 <;> rfl
  map_rel' f a := by
    cases f
    change marked (Sum.map (Fin.castLE hl) (Fin.castLE hr) (a 0)) ↔ marked (a 0)
    cases a 0 <;> rfl

private theorem marked_iff_embedding {L : Language} [L.Structure (Points A)] [L.Structure (Points B)]
    (r : L.Relations 1)
    (relA : ∀ a : Fin 1 → Points A, Language.Structure.RelMap r a ↔ marked (a 0))
    (relB : ∀ b : Fin 1 → Points B, Language.Structure.RelMap r b ↔ marked (b 0))
    (e : Points A ↪[L] Points B) (x : Points A) :
    marked (e x) ↔ marked x := by
  have h := e.map_rel r (fun _ => x)
  rw [relA, relB] at h
  exact h

private theorem exists_inl_image (e : Points A ↪ Points B)
    (hm : ∀ x, marked (e x) ↔ marked x) (x : Fin A.marked) :
    ∃ y : Fin B.marked, e (.inl x) = .inl y := by
  have h := (hm (.inl x)).mpr trivial
  cases he : e (.inl x) with
  | inl y => exact ⟨y, rfl⟩
  | inr y => rw [he] at h; contradiction

private theorem exists_inr_image (e : Points A ↪ Points B)
    (hm : ∀ x, marked (e x) ↔ marked x) (x : Fin A.unmarked) :
    ∃ y : Fin B.unmarked, e (.inr x) = .inr y := by
  have h := (hm (.inr x)).not.mpr not_false
  cases he : e (.inr x) with
  | inr y => exact ⟨y, rfl⟩
  | inl y => rw [he] at h; exact (h trivial).elim

private theorem left_rank (e : Points A ↪[expandedLanguage] Points B)
    (l : Fin A.marked → Fin B.marked) (hl : ∀ i, e (.inl i) = .inl (l i)) (i : Fin A.marked) :
    (l i).val = i.val := by
  apply rank_eq_of_preserves_pred (fun i => (l i).val)
  · intro j k hj
    have he : e (.inl j) = e (.inl k) := by rw [hl, hl, Fin.ext hj]
    exact Sum.inl_injective (e.injective he)
  · intro j
    have h := e.map_fun PredSymbol.pred (fun _ => Sum.inl j)
    change e (.inl (finPred j)) = Sum.map finPred finPred (e (.inl j)) at h
    rw [hl, hl] at h
    exact congrArg Fin.val (Sum.inl_injective h)

private theorem right_rank (e : Points A ↪[expandedLanguage] Points B)
    (r : Fin A.unmarked → Fin B.unmarked) (hr : ∀ i, e (.inr i) = .inr (r i)) (i : Fin A.unmarked) :
    (r i).val = i.val := by
  apply rank_eq_of_preserves_pred (fun i => (r i).val)
  · intro j k hj
    have he : e (.inr j) = e (.inr k) := by rw [hr, hr, Fin.ext hj]
    exact Sum.inr_injective (e.injective he)
  · intro j
    have h := e.map_fun PredSymbol.pred (fun _ => Sum.inr j)
    change e (.inr (finPred j)) = Sum.map finPred finPred (e (.inr j)) at h
    rw [hr, hr] at h
    exact congrArg Fin.val (Sum.inr_injective h)

/-- An expanded embedding exists exactly when the two prefixes fit. -/
theorem nonempty_expandedEmbedding_iff :
    Nonempty (Points A ↪[expandedLanguage] Points B) ↔
      A.marked ≤ B.marked ∧ A.unmarked ≤ B.unmarked := by
  constructor
  · rintro ⟨e⟩
    have hm := marked_iff_embedding MarkSymbol.mark (fun _ => Iff.rfl) (fun _ => Iff.rfl) e
    choose l hl using exists_inl_image e.toEmbedding hm
    choose r hr using exists_inr_image e.toEmbedding hm
    have bound {m n : ℕ} (f : Fin m → Fin n) (h : ∀ i, (f i).val = i.val) : m ≤ n := by
      by_contra! hn
      have hi := (f ⟨n, hn⟩).isLt
      rw [h] at hi
      exact (lt_irrefl _ hi)
    exact ⟨bound l (left_rank e l hl), bound r (right_rank e r hr)⟩
  · rintro ⟨hl, hr⟩
    exact ⟨embedExpanded hl hr⟩

/-- Between expanded profiles there is at most one embedding. -/
instance : Subsingleton (Points A ↪[expandedLanguage] Points B) where
  allEq e d := by
    have he := marked_iff_embedding MarkSymbol.mark (fun _ => Iff.rfl) (fun _ => Iff.rfl) e
    have hd := marked_iff_embedding MarkSymbol.mark (fun _ => Iff.rfl) (fun _ => Iff.rfl) d
    choose el hel using exists_inl_image e.toEmbedding he
    choose er her using exists_inr_image e.toEmbedding he
    choose dl hdl using exists_inl_image d.toEmbedding hd
    choose dr hdr using exists_inr_image d.toEmbedding hd
    ext x
    cases x with
    | inl i =>
      change e.toEmbedding (.inl i) = d.toEmbedding (.inl i)
      rw [hel, hdl, Fin.ext ((left_rank e el hel i).trans (left_rank d dl hdl i).symm)]
    | inr i =>
      change e.toEmbedding (.inr i) = d.toEmbedding (.inr i)
      rw [her, hdr, Fin.ext ((right_rank e er her i).trans (right_rank d dr hdr i).symm)]

/-- Joint embeddings and amalgams of expanded profiles use coordinatewise maxima. -/
def join (A B : Profile) : Profile :=
  ⟨max A.marked B.marked, max A.unmarked B.unmarked, max_le A.marked_le B.marked_le⟩

theorem expanded_amalgamation (e : Points A ↪[expandedLanguage] Points B)
    (d : Points A ↪[expandedLanguage] Points C) :
    ∃ (f : Points B ↪[expandedLanguage] Points (join B C))
      (g : Points C ↪[expandedLanguage] Points (join B C)), f.comp e = g.comp d :=
  ⟨embedExpanded (le_max_left _ _) (le_max_left _ _),
    embedExpanded (le_max_right _ _) (le_max_right _ _), Subsingleton.elim _ _⟩

/-- Every expanded target is already a Ramsey witness because the embedding
of any fixed source into it is unique whenever it exists. -/
theorem expanded_ramsey {r : ℕ} (c : (Points A ↪[expandedLanguage] Points B) → Fin r) :
    ∃ f : Points B ↪[expandedLanguage] Points B,
      ∀ e d : Points A ↪[expandedLanguage] Points B, c (f.comp e) = c (f.comp d) :=
  ⟨Language.Embedding.refl _ _, fun _ _ => congrArg c (Subsingleton.elim _ _)⟩

/-- The source is the structure with one marked point and no unmarked points. -/
def source : Profile := ⟨1, 0, by decide⟩

/-- The obstruction target consists of the two marked points. -/
def target : Profile := ⟨2, 0, by decide⟩

/-- The genuine copies of the source are represented by their marked point,
because a singleton has a unique embedding onto each one-point image. -/
def singletonEmbedding (i : Fin A.marked) : Points source ↪[reductLanguage] Points A :=
  embedReduct ⟨fun _ => i, fun x y _ => Fin.ext (by
      have hx : x.val < 1 := x.isLt
      have hy : y.val < 1 := y.isLt
      omega)⟩
    ⟨Fin.elim0, fun x => Fin.elim0 x⟩

/-- Every reduct copy of the two-point target in a profile contains both
colours under the colouring of marked singleton copies by their indices. -/
theorem markedSingleton_twoColours (f : Points target ↪[reductLanguage] Points A) :
    ∃ i j : Fin A.marked,
      f (.inl (0 : Fin 2)) = .inl i ∧ f (.inl (1 : Fin 2)) = .inl j ∧
        Fin.castLE A.marked_le i ≠ Fin.castLE A.marked_le j := by
  have hm := marked_iff_embedding MarkSymbol.mark (fun _ => Iff.rfl) (fun _ => Iff.rfl) f
  obtain ⟨i, hi⟩ := exists_inl_image f.toEmbedding hm (⟨0, by decide⟩ : Fin target.marked)
  obtain ⟨j, hj⟩ := exists_inl_image f.toEmbedding hm (⟨1, by decide⟩ : Fin target.marked)
  refine ⟨i, j, hi, hj, fun h => ?_⟩
  have hij := (Fin.castLEEmb A.marked_le).injective h
  have eq : f (.inl (0 : Fin 2)) = f (.inl (1 : Fin 2)) := hi.trans (hj.trans (congrArg Sum.inl hij.symm)).symm
  exact (by decide : (0 : Fin 2) ≠ 1) (Sum.inl_injective (f.injective eq))

private theorem reduct_embedding_components (e : Points A ↪[reductLanguage] Points B) :
    ∃ (l : Fin A.marked ↪ Fin B.marked) (r : Fin A.unmarked ↪ Fin B.unmarked),
      (∀ i, e (.inl i) = .inl (l i)) ∧ (∀ j, e (.inr j) = .inr (r j)) := by
  have hm := marked_iff_embedding MarkSymbol.mark (fun _ => Iff.rfl) (fun _ => Iff.rfl) e
  choose l hl using exists_inl_image e.toEmbedding hm
  choose r hr using exists_inr_image e.toEmbedding hm
  have hli : Injective l := by
    intro i j h
    apply Sum.inl_injective
    apply e.toEmbedding.injective
    rw [hl, hl, h]
  have hri : Injective r := by
    intro i j h
    apply Sum.inr_injective
    apply e.toEmbedding.injective
    rw [hr, hr, h]
  exact ⟨⟨l, hli⟩, ⟨r, hri⟩, hl, hr⟩

/-- Reasonableness on canonical finite profiles. The source expansion is
preserved, and the lifted target expansion is isomorphic to its canonical
prefix representative. -/
theorem expanded_reasonable (e : Points A ↪[reductLanguage] Points B) :
    ∃ (s : expandedLanguage.Structure (Points B))
      (_ : @Language.LHom.IsExpansionOn reductLanguage expandedLanguage inclusion (Points B) (profileReductStructure B) s)
      (d : @Language.Embedding expandedLanguage (Points A) (Points B) (profileExpandedStructure A) s),
      (∀ x, d x = e x) ∧
      Nonempty (@Language.Equiv expandedLanguage (Points B) (Points B) (profileExpandedStructure B) s) := by
  obtain ⟨l, r, hl, hr⟩ := reduct_embedding_components e
  have lp : A.marked ≤ B.marked := by
    simpa using Fintype.card_le_of_injective l l.injective
  have rp : A.unmarked ≤ B.unmarked := by
    simpa using Fintype.card_le_of_injective r r.injective
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ l (Fin.castLEEmb lp).injective l.injective
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair _ r (Fin.castLEEmb rp).injective r.injective
  let p := σ.sumCongr τ
  let s : expandedLanguage.Structure (Points B) :=
    expandedStructure (σ ∘ finPred ∘ σ.symm) (τ ∘ finPred ∘ τ.symm)
  let iso : @Language.Equiv expandedLanguage (Points B) (Points B) (profileExpandedStructure B) s :=
    @Language.Equiv.mk expandedLanguage (Points B) (Points B) (profileExpandedStructure B) s p (by
      intro n f a
      cases f
      change Sum.map σ τ (Sum.map finPred finPred (a 0)) =
        Sum.map (σ ∘ finPred ∘ σ.symm) (τ ∘ finPred ∘ τ.symm) (Sum.map σ τ (a 0))
      cases a 0 <;> simp) (by
      intro n R a
      cases R
      change marked (Sum.map σ τ (a 0)) ↔ marked (a 0)
      cases a 0 <;> rfl)
  have hexp : @Language.LHom.IsExpansionOn reductLanguage expandedLanguage inclusion (Points B) (profileReductStructure B) s := {
    map_onFunction f := Empty.elim f
    map_onRelation R a := by
      cases R
      rfl }
  let d : @Language.Embedding expandedLanguage (Points A) (Points B) (profileExpandedStructure A) s :=
    @Language.Embedding.comp expandedLanguage (Points A) (Points B)
      (profileExpandedStructure A) (profileExpandedStructure B) (Points B) s
      (@Language.Equiv.toEmbedding expandedLanguage (Points B) (Points B)
        (profileExpandedStructure B) s iso) (embedExpanded lp rp)
  refine ⟨s, hexp, d, ?_, ⟨iso⟩⟩
  intro x
  cases x with
  | inl i =>
    change Sum.inl (σ (Fin.castLE lp i)) = e (.inl i)
    rw [hl]
    exact congrArg Sum.inl (hσ i)
  | inr i =>
    change Sum.inr (τ (Fin.castLE rp i)) = e (.inr i)
    rw [hr]
    exact congrArg Sum.inr (hτ i)

private theorem finite_pred_closed_eq_prefix (s : Set ℕ) (hs : s.Finite)
    (hpred : ∀ x ∈ s, x - 1 ∈ s) : ∃ n, ∀ x, x ∈ s ↔ x < n := by
  classical
  have below {x y : ℕ} (hy : y ∈ s) (hxy : x ≤ y) : x ∈ s := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hxy
    induction k with
    | zero => simpa using hy
    | succ k ih =>
      apply ih
      have hm := hpred (x + k.succ) hy
      · rwa [show x + k.succ - 1 = x + k by omega] at hm
      · omega
  by_cases hn : hs.toFinset.Nonempty
  · let m := hs.toFinset.max' hn
    have hm : m ∈ s := hs.mem_toFinset.mp (Finset.max'_mem _ _)
    refine ⟨m + 1, fun x => ⟨?_, ?_⟩⟩
    · intro hx
      exact Nat.lt_succ_of_le (Finset.le_max' _ _ (hs.mem_toFinset.mpr hx))
    · exact fun hx => below hm (Nat.le_of_lt_succ hx)
  · refine ⟨0, fun x => ⟨fun hx => ?_, fun hx => (Nat.not_lt_zero _ hx).elim⟩⟩
    exact (hn ⟨x, hs.mem_toFinset.mpr hx⟩).elim

/-- Every finite closed subset of the expanded limit is a pair of prefixes,
with at most two elements in the marked prefix. -/
theorem finite_expanded_substructure_prefix (S : expandedLanguage.Substructure Limit)
    [Finite S] : ∃ A : Profile, ∀ x : Limit, x ∈ S ↔ x ∈ Set.range (embedLimit A) := by
  let left : Set ℕ := {n | ∃ i : Fin 2, i.val = n ∧ Sum.inl i ∈ S}
  let right : Set ℕ := {n | Sum.inr n ∈ S}
  have fl : left.Finite := by
    apply Set.Finite.subset (Set.finite_range (@Fin.val 2))
    rintro n ⟨i, hi, _⟩
    exact ⟨i, hi⟩
  have fr : right.Finite := by
    let f : right → S := fun x => ⟨Sum.inr x.val, x.property⟩
    let : Finite right := Finite.of_injective f fun _ _ h =>
      Subtype.ext (Sum.inr_injective (congrArg Subtype.val h))
    exact Set.toFinite _
  have hl (x : ℕ) (hx : x ∈ left) : x - 1 ∈ left := by
    obtain ⟨i, rfl, hi⟩ := hx
    exact ⟨finPred i, rfl, S.fun_mem PredSymbol.pred (fun _ => Sum.inl i) (fun _ => hi)⟩
  have hr (x : ℕ) (hx : x ∈ right) : x - 1 ∈ right :=
    S.fun_mem PredSymbol.pred (fun _ => Sum.inr x) (fun _ => hx)
  obtain ⟨m, hm⟩ := finite_pred_closed_eq_prefix _ fl hl
  obtain ⟨n, hn⟩ := finite_pred_closed_eq_prefix _ fr hr
  have m_le : m ≤ 2 := by
    by_contra! h
    obtain ⟨i, hi, _⟩ := (hm 2).mpr h
    exact i.isLt.ne hi
  let A : Profile := ⟨m, n, m_le⟩
  refine ⟨A, ?_⟩
  rintro (i | j)
  · have hm' : Sum.inl i ∈ S ↔ i.val < m := by
      refine ⟨fun h => (hm _).mp ⟨i, rfl, h⟩, fun h => ?_⟩
      obtain ⟨y, hy, hmem⟩ := (hm _).mpr h
      rwa [Fin.ext hy] at hmem
    constructor
    · intro h
      exact ⟨Sum.inl ⟨i.val, hm'.mp h⟩, by change Sum.inl _ = _; congr⟩
    · rintro ⟨y, hy⟩
      cases y with
      | inl y =>
        have h : (Fin.castLE m_le y) = i := Sum.inl_injective hy
        exact hm'.mpr (by rw [← h]; exact y.isLt)
      | inr y => cases hy
  · constructor
    · intro h
      exact ⟨Sum.inr ⟨j, (hn _).mp h⟩, rfl⟩
    · rintro ⟨y, hy⟩
      cases y with
      | inl y => cases hy
      | inr y =>
        have h : y.val = j := Sum.inr_injective hy
        exact (hn _).mpr (h ▸ y.isLt)

/-- The finite age of the expanded limit is represented by the canonical
profiles. -/
theorem finite_expanded_age_representatives (S : expandedLanguage.Substructure Limit)
    [Finite S] : ∃ A : Profile, Nonempty (Points A ≃[expandedLanguage] S) := by
  obtain ⟨A, hA⟩ := finite_expanded_substructure_prefix S
  let d := embedLimit A
  have he : d.toHom.range = S := by
    ext x
    exact (Language.Hom.mem_range.trans (hA x).symm)
  exact ⟨A, ⟨he ▸ d.equivRange⟩⟩

/-- Given a reduct embedding, the induced injection on genuine copies of
the marked singleton sends a marked point to its image. -/
noncomputable def mapSingleton (f : Points B ↪[reductLanguage] Points A)
    (i : Fin B.marked) : Fin A.marked :=
  (exists_inl_image f.toEmbedding
    (marked_iff_embedding MarkSymbol.mark (fun _ => Iff.rfl) (fun _ => Iff.rfl) f) i).choose

private theorem mapSingleton_eq (f : Points B ↪[reductLanguage] Points A)
    (i : Fin B.marked) : f (.inl i) = .inl (mapSingleton f i) :=
  (exists_inl_image f.toEmbedding
    (marked_iff_embedding MarkSymbol.mark (fun _ => Iff.rfl) (fun _ => Iff.rfl) f) i).choose_spec

private theorem mapSingleton_injective (f : Points B ↪[reductLanguage] Points A) :
    Injective (mapSingleton f) := by
  intro i j h
  apply Sum.inl_injective
  apply f.injective
  rw [mapSingleton_eq, mapSingleton_eq, h]

/-- The colour bound on actual one-point range copies of the marked source. -/
def SingletonCopyDegreeLE (t : ℕ) : Prop :=
  ∀ (B : Profile) (r : ℕ), 0 < r →
    ∃ A : Profile, ∀ colour : Fin A.marked → Fin r,
      ∃ f : Points B ↪[reductLanguage] Points A,
        (Finset.univ.image (colour ∘ mapSingleton f)).card ≤ t

/-- The marked singleton has copy Ramsey degree exactly two despite its
unique expansion type. -/
theorem markedSingleton_copyRamseyDegree_two :
    SingletonCopyDegreeLE 2 ∧ ¬ SingletonCopyDegreeLE 1 := by
  constructor
  · intro B r hr
    refine ⟨B, fun colour => ⟨Language.Embedding.refl _ _, ?_⟩⟩
    calc
      _ ≤ (Finset.univ : Finset (Fin B.marked)).card := Finset.card_image_le
      _ = B.marked := by simp
      _ ≤ 2 := B.marked_le
  · intro h
    obtain ⟨A, hA⟩ := h target 2 (by decide)
    obtain ⟨f, hf⟩ := hA (Fin.castLE A.marked_le)
    have hi : Injective (Fin.castLE A.marked_le ∘ mapSingleton f) :=
      (Fin.castLEEmb A.marked_le).injective.comp (mapSingleton_injective f)
    have ht : (Finset.univ : Finset (Fin target.marked)).card = 2 := by
      rw [Finset.card_univ, Fintype.card_fin]
      rfl
    rw [Finset.card_image_of_injective _ hi, ht] at hf
    omega

/-- A unary operation on the marked singleton has a unique interpretation.
Thus every prescribed expansion of the source on its underlying set is
isomorphic to the realised canonical expansion, which embeds into the limit. -/
theorem markedSingleton_unique_expansion
    (s : expandedLanguage.Structure (Points source))
    (hs : @Language.LHom.IsExpansionOn reductLanguage expandedLanguage inclusion
      (Points source) (profileReductStructure source) s) :
    Nonempty (@Language.Equiv expandedLanguage (Points source) (Points source) s (profileExpandedStructure source)) := by
  have single (x y : Points source) : x = y := by
    change Fin 1 ⊕ Fin 0 at x y
    rcases x with i | i
    · rcases y with j | j
      · exact congrArg Sum.inl (Subsingleton.elim i j)
      · exact Fin.elim0 j
    · exact Fin.elim0 i
  refine ⟨@Language.Equiv.mk expandedLanguage (Points source) (Points source)
    s (profileExpandedStructure source) (Equiv.refl _) (fun _ _ => single _ _) ?_⟩
  intro n r a
  cases r
  have hr := @Language.LHom.IsExpansionOn.map_onRelation reductLanguage expandedLanguage
    inclusion (Points source) (profileReductStructure source) s hs 1 MarkSymbol.mark a
  exact iff_of_eq hr.symm

/-- Every finite reduct substructure is isomorphic to a profile.
Conversely every profile occurs in the reduct of an expanded prefix. -/
theorem finite_reduct_age_representatives (S : reductLanguage.Substructure Limit)
    [Finite S] : ∃ A : Profile, Nonempty (Points A ≃[reductLanguage] S) := by
  classical
  let L := {i : Fin 2 // Sum.inl i ∈ S}
  let R := {i : ℕ // Sum.inr i ∈ S}
  let into : L ⊕ R → S
    | .inl x => ⟨.inl x.val, x.property⟩
    | .inr x => ⟨.inr x.val, x.property⟩
  have hi : Injective into := by
    rintro (i | j) (i' | j') h
    · exact congrArg Sum.inl (Subtype.ext (Sum.inl_injective (congrArg Subtype.val h)))
    · exact (Sum.inl_ne_inr (congrArg Subtype.val h)).elim
    · exact (Sum.inr_ne_inl (congrArg Subtype.val h)).elim
    · exact congrArg Sum.inr (Subtype.ext (Sum.inr_injective (congrArg Subtype.val h)))
  have hs : Surjective into := by
    rintro ⟨i | j, h⟩
    · exact ⟨.inl ⟨i, h⟩, rfl⟩
    · exact ⟨.inr ⟨j, h⟩, rfl⟩
  let : Finite R := Finite.of_injective _ (hi.comp Sum.inr_injective)
  let : Fintype L := Fintype.ofFinite _
  let : Fintype R := Fintype.ofFinite _
  have hcap : Fintype.card L ≤ 2 := by
    simpa using Fintype.card_le_of_injective (fun x : L => x.val) Subtype.val_injective
  let A : Profile := ⟨Fintype.card L, Fintype.card R, hcap⟩
  let e : Points A ≃ S := ((Fintype.equivFin L).symm.sumCongr
    (Fintype.equivFin R).symm).trans (Equiv.ofBijective into ⟨hi, hs⟩)
  refine ⟨A, ⟨@Language.Equiv.mk reductLanguage (Points A) S (profileReductStructure A)
    inferInstance e (fun f _ => Empty.elim f) ?_⟩⟩
  intro n p a
  cases p
  change marked (e (a 0)).val ↔ marked (a 0)
  cases a 0 <;> rfl

/-- Restrict a first-order embedding to the unary-predicate reduct. -/
def forgetEmbedding {X Y : Type*} [reductLanguage.Structure X] [reductLanguage.Structure Y]
    [expandedLanguage.Structure X] [expandedLanguage.Structure Y]
    [inclusion.IsExpansionOn X] [inclusion.IsExpansionOn Y]
    (f : X ↪[expandedLanguage] Y) : X ↪[reductLanguage] Y where
  toEmbedding := f.toEmbedding
  map_fun' g := Empty.elim g
  map_rel' r a := by
    simpa only [inclusion.map_onRelation] using f.map_rel' (inclusion.onRelation r) a

/-- Every reduct profile occurs in the reduct age of the same limit. -/
def embedReductLimit (A : Profile) : Points A ↪[reductLanguage] Limit :=
  forgetEmbedding (embedLimit A)

private theorem profile_le_of_reduct_embedding (e : Points A ↪[reductLanguage] Points B) :
    A.marked ≤ B.marked ∧ A.unmarked ≤ B.unmarked := by
  obtain ⟨l, r, _, _⟩ := reduct_embedding_components e
  constructor
  · simpa using Fintype.card_le_of_injective l l.injective
  · simpa using Fintype.card_le_of_injective r r.injective

private theorem profile_eq (hm : A.marked = B.marked) (hn : A.unmarked = B.unmarked) :
    A = B := by
  cases A
  cases B
  dsimp at hm hn
  subst_vars
  rfl

/-- Every expansion on a fixed finite reduct that occurs in the age is
isomorphic to its canonical prefix expansion. In particular the expansion
is precompact, with one isomorphism type per profile. -/
theorem unique_expansionType_of_embeddable (s : expandedLanguage.Structure (Points A))
    (hs : @Language.LHom.IsExpansionOn reductLanguage expandedLanguage inclusion
      (Points A) (profileReductStructure A) s)
    (h : Nonempty (@Language.Embedding expandedLanguage (Points A) Limit s inferInstance)) :
    Nonempty (@Language.Equiv expandedLanguage (Points A) (Points A) s
      (profileExpandedStructure A)) := by
  let : expandedLanguage.Structure (Points A) := s
  let : inclusion.IsExpansionOn (Points A) := hs
  obtain ⟨e⟩ := h
  let e' := e.equivRange
  let S := e.toHom.range
  let : Finite S := Finite.of_injective e'.symm e'.symm.injective
  obtain ⟨B, ⟨g⟩⟩ := finite_expanded_age_representatives S
  let g' : Points B ≃[expandedLanguage] Points A := e'.symm.comp g
  have hBA := profile_le_of_reduct_embedding (forgetEmbedding g'.toEmbedding)
  have hAB := profile_le_of_reduct_embedding (forgetEmbedding g'.symm.toEmbedding)
  have equality : B = A := profile_eq (le_antisymm hBA.1 hAB.1) (le_antisymm hBA.2 hAB.2)
  refine ⟨?_⟩
  exact equality ▸ g'.symm

/-- Reasonableness extends to every prescribed expansion of the source
admitted by the age. -/
theorem expanded_reasonable_from_any_prescribed (e : Points A ↪[reductLanguage] Points B)
    (s : expandedLanguage.Structure (Points A))
    (hs : @Language.LHom.IsExpansionOn reductLanguage expandedLanguage inclusion
      (Points A) (profileReductStructure A) s)
    (he : Nonempty (@Language.Embedding expandedLanguage (Points A) Limit s inferInstance)) :
    ∃ (t : expandedLanguage.Structure (Points B))
      (_ : @Language.LHom.IsExpansionOn reductLanguage expandedLanguage inclusion
        (Points B) (profileReductStructure B) t)
      (d : @Language.Embedding expandedLanguage (Points A) (Points B) s t),
      (∀ x, d x = e x) ∧
      Nonempty (@Language.Equiv expandedLanguage (Points B) (Points B)
        (profileExpandedStructure B) t) := by
  obtain ⟨iso⟩ := unique_expansionType_of_embeddable s hs he
  let prescribed := @Language.Equiv.toEmbedding expandedLanguage (Points A) (Points A) s
    (profileExpandedStructure A) iso
  let inv := @Language.Equiv.toEmbedding expandedLanguage (Points A) (Points A)
    (profileExpandedStructure A) s
    (@Language.Equiv.symm expandedLanguage (Points A) (Points A) s (profileExpandedStructure A) iso)
  let re := @forgetEmbedding (Points A) (Points A) (profileReductStructure A)
    (profileReductStructure A) (profileExpandedStructure A) s inferInstance hs inv
  obtain ⟨t, ht, d, hd, hiso⟩ := expanded_reasonable (e.comp re)
  refine ⟨t, ht, @Language.Embedding.comp expandedLanguage (Points A) (Points A) s
    (profileExpandedStructure A) (Points B) t d prescribed, ?_, hiso⟩
  intro x
  change d (iso x) = e x
  rw [hd]
  change e (inv (iso x)) = e x
  have hx := @Language.Equiv.symm_apply_apply expandedLanguage (Points A) (Points A)
    s (profileExpandedStructure A) iso x
  exact congrArg (e : Points A → Points B) hx

end SuccessorTree.NonPrecompact.PredecessorExpansion
