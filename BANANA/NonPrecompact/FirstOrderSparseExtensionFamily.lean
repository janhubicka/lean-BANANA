import BANANA.NonPrecompact.SparseExtensionFamily
import Mathlib.Logic.Equiv.List
import Mathlib.ModelTheory.Fraisse
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Sparse families in a homogeneous first-order structure

Strong amalgamation lets an extension be placed over a designated finite
substructure with no further intersections with a finite ambient structure.
A finite list of reduct types at each cardinality gives a finite collection of
extension requests on each source at each round.
-/

namespace SuccessorTree.NonPrecompact

open CategoryTheory FirstOrder Set
open scoped FirstOrder

universe u v w i

/-- Amalgamation in which the images meet only over the common source. -/
def FirstOrderStrongAmalgamation {L : Language.{u, v}} (K : Set (Bundled.{w} L.Structure)) :
    Prop :=
  ∀ (A C B : Bundled.{w} L.Structure) (f : A ↪[L] C) (g : A ↪[L] B),
    A ∈ K → C ∈ K → B ∈ K →
    ∃ (Q : Bundled.{w} L.Structure) (j : C ↪[L] Q) (k : B ↪[L] Q),
      Q ∈ K ∧ j.comp f = k.comp g ∧
        ∀ b : B, ∀ c : C, k b = j c → ∃ a : A, g a = b

/-- Place a finite-structure extension with no extra intersection with a
specified ambient finitely generated substructure. -/
theorem firstOrder_exists_embedding_inter_of_strongAmalgamation
    {L : Language.{u, v}} {M : Type w} [L.Structure M]
    (homogeneous : L.IsUltrahomogeneous M)
    (strong : FirstOrderStrongAmalgamation (L.age M))
    (A C : L.Substructure M) (hAC : A ≤ C) (hA : A.FG) (hC : C.FG)
    (B : Bundled.{w} L.Structure) (hB : B ∈ L.age M) (f : A ↪[L] B) :
    ∃ e : B ↪[L] M, e.comp f = A.subtype ∧
      Set.range e ∩ (C : Set M) = (A : Set M) := by
  obtain ⟨Q, j, k, hQ, hcomm, hstrong⟩ :=
    strong (Bundled.of A) (Bundled.of C) B (A.inclusion hAC) f
      (Language.age.fg_substructure hA) (Language.age.fg_substructure hC) hB
  let : Nonempty (Q ↪[L] M) := hQ.2
  obtain ⟨e, he⟩ := homogeneous.extend_embedding
    ((Language.Substructure.fg_iff_structure_fg C).1 hC) C.subtype j
  have heal (c : C) : e (j c) = (c : M) := (DFunLike.congr_fun he c).symm
  have hwrap (a : A) : e (k (f a)) = (a : M) := by
    have hcomm' : j (A.inclusion hAC a) = k (f a) := DFunLike.congr_fun hcomm a
    rw [← hcomm']
    exact heal (A.inclusion hAC a)
  refine ⟨e.comp k, Language.Embedding.ext hwrap, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨b, rfl⟩, hc⟩
    let c : C := ⟨(e.comp k) b, hc⟩
    have hmatch : k b = j c := e.injective (heal c).symm
    obtain ⟨a, ha⟩ := hstrong b c hmatch
    change e (k b) ∈ A
    rw [← ha, hwrap]
    exact a.prop
  · intro hx
    exact ⟨⟨f ⟨x, hx⟩, hwrap ⟨x, hx⟩⟩, hAC hx⟩

private noncomputable def finiteCarrier {L : Language.{u,v}} {M : Type w} [L.Structure M]
    (S : L.Substructure M) (finiteS : Finite S) : Finset M :=
  letI := finiteS
  (Set.toFinite (S : Set M)).toFinset

private theorem coe_finiteCarrier {L : Language.{u,v}} {M : Type w} [L.Structure M]
    (S : L.Substructure M) (finiteS : Finite S) :
    ((finiteCarrier S finiteS : Finset M) : Set M) = (S : Set M) :=
  Set.Finite.coe_toFinset _

private theorem card_finiteCarrier {L : Language.{u,v}} {M : Type w} [L.Structure M]
    (S : L.Substructure M) (finiteS : Finite S) :
    (finiteCarrier S finiteS).card = Nat.card S := by
  let f := finiteCarrier S finiteS
  let eq : f ≃ S := Set.equivOfEq (coe_finiteCarrier S finiteS)
  rw [← Nat.card_congr eq, Nat.card_eq_fintype_card, Fintype.card_coe]

variable {L : Language.{u,v}} {M : Type w} [L.Structure M]

private abbrev on (A : Finset M) : L.Substructure M :=
  Language.Substructure.closure L (A : Set M)

private def closedFiniteCarriers : Set (Finset M) :=
  {A | (on (L := L) A : Set M) = (A : Set M)}

private theorem mem_closedFiniteCarriers (S : L.Substructure M) (finiteS : Finite S) :
    finiteCarrier S finiteS ∈ closedFiniteCarriers (L := L) := by
  change (on (L := L) (finiteCarrier S finiteS) : Set M) = _
  simp only [on, coe_finiteCarrier, Language.Substructure.closure_eq]

private theorem closedFiniteCarriers_enlarge [DecidableEq M] [Infinite M]
    (localFinite : ∀ S : L.Substructure M, S.FG → Finite S)
    (C : Finset M) (n : ℕ) :
    ∃ D ∈ closedFiniteCarriers (L := L), C ⊆ D ∧ n ≤ D.card := by
  obtain ⟨T, hT⟩ := Finset.exists_card_eq (α := M) n
  let S := on (L := L) (C ∪ T)
  let hS : Finite S := localFinite S (Language.Substructure.fg_closure (C ∪ T).finite_toSet)
  let D := finiteCarrier S hS
  have hsub : C ∪ T ⊆ D := by
    rw [← Finset.coe_subset, coe_finiteCarrier]
    exact Language.Substructure.subset_closure
  exact ⟨D, mem_closedFiniteCarriers S hS, Finset.subset_union_left.trans hsub,
    hT ▸ Finset.card_le_card (Finset.subset_union_right.trans hsub)⟩

/-- A countable locally finite homogeneous structure with strong age amalgamation
and finitely many reduct isomorphism types at each size has a cofinal sparse
family of finite substructures that answers all reduct extension requests. -/
theorem firstOrder_exists_sparse_extension_family [DecidableEq M] [Countable M] [Infinite M]
    (localFinite : ∀ S : L.Substructure M, S.FG → Finite S)
    (homogeneous : L.IsUltrahomogeneous M)
    (strong : FirstOrderStrongAmalgamation (L.age M))
    {I : ℕ → Type i} (R : ∀ n, I n → Bundled.{w} L.Structure)
    (finiteI : ∀ n, Finite (I n))
    (memR : ∀ n j, R n j ∈ L.age M) (cardR : ∀ n j, Nat.card (R n j) = n)
    (covers : ∀ B : Bundled.{w} L.Structure, B ∈ L.age M →
      ∃ j : I (Nat.card B), Nonempty (B ≃[L] R (Nat.card B) j)) :
    ∃ F : Set (Finset M),
      (∃ A ∈ F, (A : Set M) = (Language.Substructure.closure L (∅ : Set M) : Set M)) ∧
      (∀ A ∈ F, (Language.Substructure.closure L (A : Set M) : Set M) = (A : Set M)) ∧
      (∀ C, ∃ D ∈ F, C ⊆ D) ∧
      (∀ A ∈ F, ∀ B ∈ F, A ∩ B ∈ F) ∧
      (∀ n : ℕ, {A ∈ F | A.card = n}.Finite) ∧
      ∀ A ∈ F, ∀ B : Bundled.{w} L.Structure, B ∈ L.age M →
        ∀ f : Language.Substructure.closure L (A : Set M) ↪[L] B,
          A.card < Nat.card B →
          ∃ D ∈ F, ∃ e : B ↪[L] M, e.comp f = (on (L := L) A).subtype ∧
            Set.range e = (D : Set M) := by
  classical
  let Q (A : Finset M) (n : ℕ) := Σ j : I n, on (L := L) A ↪[L] R n j
  let goal (A : Finset M) (n : ℕ) (q : Q A n) (D : Finset M) :=
    ∃ e : R n q.1 ↪[L] M, e.comp q.2 = (on (L := L) A).subtype ∧
      Set.range e = (D : Set M)
  have finiteRequests (A : Finset M) (n : ℕ) : Finite (Q A n) := by
    let : Finite (on (L := L) A) := localFinite _ (Language.Substructure.fg_closure A.finite_toSet)
    let (j : I n) : Finite (R n j) := by
      obtain ⟨embed⟩ := (memR n j).2
      have hfg := (memR n j).1.range embed.toHom
      let : Finite embed.toHom.range := localFinite _ hfg
      exact Finite.of_equiv _ embed.equivRange.symm.toEquiv
    let : Finite (I n) := finiteI n
    let (j : I n) : Finite (on (L := L) A ↪[L] R n j) :=
      Finite.of_injective DFunLike.coe DFunLike.coe_injective
    unfold Q
    infer_instance
  have fresh (A C : Finset M) (n : ℕ) (q : Q A n)
      (hA : A ∈ closedFiniteCarriers (L := L)) (hC : C ∈ closedFiniteCarriers (L := L))
      (hAC : A ⊆ C) (_hcard : A.card < n) :
      ∃ D ∈ closedFiniteCarriers (L := L), D.card = n ∧ D ∩ C = A ∧ goal A n q D := by
    have hAfg : (on (L := L) A).FG := Language.Substructure.fg_closure A.finite_toSet
    have hCfg : (on (L := L) C).FG := Language.Substructure.fg_closure C.finite_toSet
    obtain ⟨e, hcomp, hinter⟩ := firstOrder_exists_embedding_inter_of_strongAmalgamation
      homogeneous strong (on A) (on C)
      (Language.Substructure.closure_mono (Finset.coe_subset.mpr hAC)) hAfg hCfg
      (R n q.1) (memR n q.1) q.2
    let hD : Finite e.toHom.range := localFinite _ ((memR n q.1).1.range e.toHom)
    let D := finiteCarrier e.toHom.range hD
    have hD_range : (D : Set M) = Set.range e := coe_finiteCarrier _ _
    have hD_card : D.card = n := by
      rw [card_finiteCarrier, ← Nat.card_congr e.equivRange.toEquiv, cardR]
    have hD_inter : D ∩ C = A := by
      apply Finset.coe_injective
      rw [Finset.coe_inter, hD_range, ← hC, ← hA, hinter]
    exact ⟨D, mem_closedFiniteCarriers _ _, hD_card, hD_inter, e, hcomp, hD_range.symm⟩
  obtain ⟨seed, hseed⟩ := exists_surjective_nat (Finset M)
  let hbase := localFinite (Language.Substructure.closure L (∅ : Set M))
    (Language.Substructure.fg_closure Set.finite_empty)
  let base := finiteCarrier (Language.Substructure.closure L (∅ : Set M)) hbase
  obtain ⟨F, hbaseF, hFclosed, hFcofinal, hFinter, hFsize, hFextend⟩ :=
    SparseExtensionFamily.exists_sparse_extension_family goal finiteRequests
      (closedFiniteCarriers_enlarge localFinite) base (mem_closedFiniteCarriers _ _) seed
      (fun C => let ⟨n, hn⟩ := hseed C; ⟨n, hn ▸ Finset.Subset.rfl⟩) fresh
  refine ⟨F, ⟨base, hbaseF, coe_finiteCarrier _ _⟩, fun A hA => hFclosed hA,
    hFcofinal, hFinter, hFsize, ?_⟩
  intro A hA B hB f hsize
  obtain ⟨j, ⟨equiv⟩⟩ := covers B hB
  obtain ⟨D, hD, -, -, e, he, hD_range⟩ :=
    hFextend A hA (Nat.card B) hsize ⟨j, equiv.toEmbedding.comp f⟩
  refine ⟨D, hD, e.comp equiv.toEmbedding, ?_, ?_⟩
  · rw [Language.Embedding.comp_assoc]
    exact he
  · change Set.range (e ∘ equiv) = _
    rw [equiv.surjective.range_comp, hD_range]

/-- A family's extension property for its actual carriers gives the prescribed
lift for any labelled copy whose range belongs to the family. -/
theorem firstOrder_sparse_extension_family_lifts [DecidableEq M]
    (localFinite : ∀ S : L.Substructure M, S.FG → Finite S)
    (F : Set (Finset M))
    (closed : ∀ A ∈ F, (on (L := L) A : Set M) = (A : Set M))
    (extend : ∀ A ∈ F, ∀ B : Bundled.{w} L.Structure, B ∈ L.age M →
      ∀ f : on (L := L) A ↪[L] B, A.card < Nat.card B →
        ∃ D ∈ F, ∃ e : B ↪[L] M, e.comp f = (on (L := L) A).subtype ∧
          Set.range e = (D : Set M))
    (A B : Bundled.{w} L.Structure) (hB : B ∈ L.age M) (e : A ↪[L] B)
    (a : A ↪[L] M) (ha : ∃ S ∈ F, (S : Set M) = Set.range a) :
    ∃ b : B ↪[L] M, (∀ x, b (e x) = a x) ∧
      ∃ D ∈ F, (D : Set M) = Set.range b := by
  obtain ⟨S, hS, hSa⟩ := ha
  let T := on (L := L) S
  have hTa : (T : Set M) = Set.range a := (closed S hS).trans hSa
  let j := Language.Embedding.codRestrict T a (fun x => by
    change a x ∈ (T : Set M)
    rw [hTa]
    exact Set.mem_range_self x)
  have hsurj : Function.Surjective j := by
    intro x
    have hx : (x : M) ∈ Set.range a := hTa ▸ x.prop
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩
  let iso : A ≃[L] T := ⟨Equiv.ofBijective j ⟨j.injective, hsurj⟩, j.map_fun', j.map_rel'⟩
  let f : T ↪[L] B := e.comp iso.symm.toEmbedding
  have hmain :
      ∃ D ∈ F, ∃ b : B ↪[L] M, b.comp f = T.subtype ∧ Set.range b = (D : Set M) := by
    by_cases hlt : S.card < Nat.card B
    · exact extend S hS B hB f hlt
    · let eq : T ≃ ↥S := Set.equivOfEq (closed S hS)
      have hcard : Nat.card T = S.card := by
        rw [Nat.card_congr eq, Nat.card_eq_fintype_card, Fintype.card_coe]
      obtain ⟨g⟩ := hB.2
      let : Finite g.toHom.range := localFinite _ (hB.1.range g.toHom)
      let : Finite B := Finite.of_equiv _ g.equivRange.symm.toEquiv
      have hfbij : Function.Bijective f :=
        f.injective.bijective_of_nat_card_le (hcard ▸ Nat.le_of_not_gt hlt)
      let k : T ≃[L] B := ⟨Equiv.ofBijective f hfbij, f.map_fun', f.map_rel'⟩
      let b := T.subtype.comp k.symm.toEmbedding
      refine ⟨S, hS, b, ?_, ?_⟩
      · apply Language.Embedding.ext
        intro x
        change ((k.symm (k x) : T) : M) = x
        rw [k.symm_apply_apply]
      · change Set.range (T.subtype ∘ k.symm) = _
        rw [k.symm.surjective.range_comp]
        exact Subtype.range_coe.trans (closed S hS)
  obtain ⟨D, hD, b, hb, hrange⟩ := hmain
  refine ⟨b, ?_, D, hD, hrange.symm⟩
  intro x
  have hh := DFunLike.congr_fun hb (iso x)
  change b (e (iso.symm (iso x))) = a x at hh
  simpa only [iso.symm_apply_apply] using hh

end SuccessorTree.NonPrecompact
