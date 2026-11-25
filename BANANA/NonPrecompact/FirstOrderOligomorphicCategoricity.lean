import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import BANANA.NonPrecompact.FirstOrderPointwiseAutomorphism
import BANANA.NonPrecompact.FirstOrderTupleOrbits

/-!
# Countable categoricity from finite tuple-orbit quotients

Finite orbit covers give finite covers by realised formula types. Each realised
type is isolated by finitely many distinguishing formulas, and that isolation
transfers to every elementarily equivalent structure. Realising one more
coordinate then gives a back-and-forth system on finite tuples. This proves
the forward implication of Ryll–Nardzewski for the complete theory of any
first-order structure with finite tuple-orbit quotients.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

universe u v w w'

variable {L : Language.{u, v}} {A : Type w} {B : Type w'}
variable [L.Structure A] [L.Structure B]

/-- Two finite tuples agree on all first-order formulas without parameters. -/
def SameFormulaType {n : ℕ} (a : Fin n → A) (b : Fin n → B) : Prop :=
  ∀ φ : L.Formula (Fin n), φ.Realize a ↔ φ.Realize b

theorem SameFormulaType.refl {n : ℕ} (a : Fin n → A) :
    SameFormulaType (L := L) a a := fun _ => Iff.rfl

theorem SameFormulaType.symm {n : ℕ} {a : Fin n → A} {b : Fin n → B}
    (h : SameFormulaType (L := L) a b) : SameFormulaType (L := L) b a :=
  fun φ => (h φ).symm

theorem SameFormulaType.trans {C : Type*} [L.Structure C] {n : ℕ}
    {a : Fin n → A} {b : Fin n → B} {c : Fin n → C}
    (hab : SameFormulaType (L := L) a b) (hbc : SameFormulaType (L := L) b c) :
    SameFormulaType (L := L) a c :=
  fun φ => (hab φ).trans (hbc φ)

/-- Universal satisfaction of a formula transfers by elementary equivalence. -/
theorem forall_realize_of_elementarilyEquivalent (hAB : A ≅[L] B)
    {n : ℕ} (φ : L.Formula (Fin n))
    (h : ∀ a : Fin n → A, φ.Realize a) :
    ∀ b : Fin n → B, φ.Realize b := by
  let σ : L.Sentence := (φ.relabel (Sum.inr : Fin n → Empty ⊕ Fin n)).iAlls (Fin n)
  have hs : A ⊨ σ := by
    simpa [σ, Language.Sentence.Realize, Function.comp_def] using h
  have ht := (Language.elementarilyEquivalent_iff.mp hAB σ).mp hs
  simpa [σ, Language.Sentence.Realize, Function.comp_def] using ht

/-- Finite tuple-type covers in a structure give an isolating formula for
each realised type in that structure. -/
theorem exists_formula_isolates_in_finite_type_cover {n : ℕ} {ι : Type*} [Finite ι]
    (r : ι → Fin n → A)
    (hc : ∀ b : Fin n → A, ∃ i, SameFormulaType (L := L) (r i) b)
    (a : Fin n → A) :
    ∃ φ : L.Formula (Fin n), ∀ b : Fin n → A,
      φ.Realize b ↔ SameFormulaType (L := L) a b := by
  classical
  have hsep (i : ι) : ∃ φ : L.Formula (Fin n), φ.Realize a ∧
      (φ.Realize (r i) → SameFormulaType (L := L) a (r i)) := by
    by_cases h : SameFormulaType (L := L) a (r i)
    · exact ⟨⊤, by simp, fun _ => h⟩
    · unfold SameFormulaType at h
      obtain ⟨ψ, hψ⟩ := not_forall.mp h
      by_cases ha : ψ.Realize a
      · exact ⟨ψ, ha, fun hb => (hψ (iff_of_true ha hb)).elim⟩
      · refine ⟨ψ.not, Language.Formula.realize_not.mpr ha, fun hb => ?_⟩
        exact (hψ (iff_of_false ha (Language.Formula.realize_not.mp hb))).elim
  choose d hd using hsep
  refine ⟨Language.Formula.iInf d, fun b => ?_⟩
  constructor
  · intro hb
    obtain ⟨i, hi⟩ := hc b
    have hr := (hi (d i)).mpr ((Language.Formula.realize_iInf.mp hb) i)
    exact (hd i).2 hr |>.trans hi
  · intro h
    exact Language.Formula.realize_iInf.mpr fun i => (h (d i)).mp (hd i).1

/-- An isolating formula from one structure continues to isolate the
same full type in every elementarily equivalent structure. -/
theorem isolates_formula_type_of_elementarilyEquivalent (hAB : A ≅[L] B)
    {n : ℕ} {φ : L.Formula (Fin n)} {a : Fin n → A}
    (hφ : ∀ b : Fin n → A, φ.Realize b ↔ SameFormulaType (L := L) a b)
    (b : Fin n → B) :
    φ.Realize b ↔ SameFormulaType (L := L) a b := by
  constructor
  · intro hb ψ
    by_cases ha : ψ.Realize a
    · have h := forall_realize_of_elementarilyEquivalent hAB (φ.imp ψ) fun c =>
        Language.Formula.realize_imp.mpr fun hc => ((hφ c).mp hc ψ).mp ha
      exact iff_of_true ha (Language.Formula.realize_imp.mp (h b) hb)
    · have h := forall_realize_of_elementarilyEquivalent hAB (φ.imp ψ.not) fun c =>
        Language.Formula.realize_imp.mpr fun hc =>
          Language.Formula.realize_not.mpr (ha ∘ ((hφ c).mp hc ψ).mpr)
      exact iff_of_false ha (Language.Formula.realize_not.mp (Language.Formula.realize_imp.mp (h b) hb))
  · intro hb
    exact (hb φ).mp ((hφ a).mpr (SameFormulaType.refl a))

/-- A finite cover by full realised types remains a cover of every
elementarily equivalent model, with one isolating formula for each
representative. -/
theorem finite_formula_type_cover_of_elementarilyEquivalent (hAB : A ≅[L] B)
    {n : ℕ} {ι : Type*} [Finite ι] (r : ι → Fin n → A)
    (hc : ∀ b : Fin n → A, ∃ i, SameFormulaType (L := L) (r i) b) :
    ∀ b : Fin n → B, ∃ i, SameFormulaType (L := L) (r i) b := by
  classical
  choose d hd using fun i => exists_formula_isolates_in_finite_type_cover r hc (r i)
  have h := forall_realize_of_elementarilyEquivalent hAB (Language.Formula.iSup d) fun a => by
    obtain ⟨i, hi⟩ := hc a
    exact Language.Formula.realize_iSup.mpr ⟨i, (hd i a).mpr hi⟩
  intro b
  obtain ⟨i, hi⟩ := Language.Formula.realize_iSup.mp (h b)
  exact ⟨i, (isolates_formula_type_of_elementarilyEquivalent hAB (hd i) b).mp hi⟩

/-- Automorphism-orbit representatives are a finite formula-type cover. -/
theorem formula_type_cover_of_finset_automorphism_orbit_representatives {n : ℕ}
    (R : Finset (Fin n → A))
    (hR : ∀ b : Fin n → A, ∃ a ∈ R, ∃ g : FirstOrderAut L A, g • a = b) :
    ∀ b : Fin n → A, ∃ a : R, SameFormulaType (L := L) a.val b := by
  intro b
  obtain ⟨a, ha, g, rfl⟩ := hR b
  exact ⟨⟨a, ha⟩, fun φ => (Language.StrongHomClass.realize_formula g.toEquiv φ).symm⟩

private structure MatchedTuple (n : ℕ) where
  left : Fin n → A
  right : Fin n → B
  same : SameFormulaType (L := L) left right

/-- A matching pair of finite tuples extends to an isomorphism if
matching tuple types have one-point extensions on either side. -/
theorem exists_equiv_of_formulaType_backAndForth [Countable A] [Countable B]
    [Nonempty A] [Nonempty B]
    {k : ℕ} {a₀ : Fin k → A} {b₀ : Fin k → B}
    (seed : SameFormulaType (L := L) a₀ b₀)
    (forth : ∀ {n} {a : Fin n → A} {b : Fin n → B}, SameFormulaType (L := L) a b →
      ∀ x, ∃ y, SameFormulaType (L := L) (Fin.snoc a x) (Fin.snoc b y))
    (back : ∀ {n} {a : Fin n → A} {b : Fin n → B}, SameFormulaType (L := L) a b →
      ∀ y, ∃ x, SameFormulaType (L := L) (Fin.snoc a x) (Fin.snoc b y)) :
    ∃ e : A ≃[L] B, ∀ i, e (a₀ i) = b₀ i := by
  classical
  obtain ⟨u, hu⟩ := exists_surjective_nat A
  obtain ⟨v, hv⟩ := exists_surjective_nat B
  let step (n : ℕ) (p : MatchedTuple (L := L) (A := A) (B := B) (k + n)) :
      MatchedTuple (L := L) (A := A) (B := B) (k + (n + 1)) :=
    if n % 2 = 0 then
      let h := forth p.same (u (n / 2))
      ⟨Fin.snoc p.left (u (n / 2)), Fin.snoc p.right h.choose, h.choose_spec⟩
    else
      let h := back p.same (v (n / 2))
      ⟨Fin.snoc p.left h.choose, Fin.snoc p.right (v (n / 2)), h.choose_spec⟩
  let chain : ∀ n, MatchedTuple (L := L) (A := A) (B := B) (k + n) :=
    Nat.rec ⟨a₀, b₀, seed⟩ step
  have extend {n m : ℕ} (h : n ≤ m) (i : Fin (k + n)) :
      (chain m).left (i.castLE (Nat.add_le_add_left h k)) = (chain n).left i ∧
        (chain m).right (i.castLE (Nat.add_le_add_left h k)) = (chain n).right i := by
    induction m, h using Nat.le_induction with
    | base => simp
    | succ m h ih =>
      have he : i.castLE (Nat.add_le_add_left (Nat.le.step h) k) =
          (i.castLE (Nat.add_le_add_left h k)).castSucc := Fin.ext rfl
      rw [he]
      change (step m (chain m)).left _ = _ ∧ (step m (chain m)).right _ = _
      unfold step
      split <;> simpa only [Fin.snoc_castSucc] using ih
  have left_total (x : A) : ∃ (n : ℕ) (i : Fin (k + n)), (chain n).left i = x := by
    obtain ⟨j, rfl⟩ := hu x
    refine ⟨2 * j + 1, Fin.last _, ?_⟩
    change (step (2 * j) (chain (2 * j))).left (Fin.last _) = _
    have hdiv : 2 * j / 2 = j := by omega
    simp [step, hdiv]
  have right_total (y : B) : ∃ (n : ℕ) (i : Fin (k + n)), (chain n).right i = y := by
    obtain ⟨j, rfl⟩ := hv y
    refine ⟨2 * j + 1 + 1, Fin.last _, ?_⟩
    change (step (2 * j + 1) (chain (2 * j + 1))).right (Fin.last _) = _
    have hdiv : (2 * j + 1) / 2 = j := by omega
    simp [step, hdiv]
  have eq_at {n m : ℕ} (i : Fin (k + n)) (j : Fin (k + m)) :
      (chain n).left i = (chain m).left j ↔ (chain n).right i = (chain m).right j := by
    let a := i.castLE (Nat.add_le_add_left (le_max_left n m) k)
    let b := j.castLE (Nat.add_le_add_left (le_max_right n m) k)
    have ht := (chain (max n m)).same ((Language.Term.var a).equal (Language.Term.var b))
    simpa only [Language.Formula.realize_equal, Language.Term.realize_var,
      a, b, (extend (le_max_left n m) i).1, (extend (le_max_left n m) i).2,
      (extend (le_max_right n m) j).1, (extend (le_max_right n m) j).2] using ht
  let f (x : A) : B := (chain (left_total x).choose).right (left_total x).choose_spec.choose
  have f_apply {n : ℕ} (i : Fin (k + n)) : f ((chain n).left i) = (chain n).right i :=
    (eq_at _ _).mp (left_total _).choose_spec.choose_spec
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨n, i, hi⟩ := right_total b
    exact ⟨(chain n).left i, (f_apply i).trans hi⟩
  let e : A ↪ₑ[L] B := {
    toFun := f
    map_formula' := by
      intro m φ x
      choose n i hi using fun j : Fin m => left_total (x j)
      let N := Finset.univ.sup n
      let j (t : Fin m) : Fin (k + N) :=
        (i t).castLE (Nat.add_le_add_left (Finset.le_sup (Finset.mem_univ t)) k)
      have hleft : (chain N).left ∘ j = x := by
        funext t
        have ht : n t ≤ N := Finset.le_sup (Finset.mem_univ t)
        exact ((extend ht (i t)).1).trans (hi t)
      have hright : (chain N).right ∘ j = f ∘ x := by
        funext k
        rw [Function.comp_apply, ← hleft]
        exact (f_apply (j k)).symm
      have h := (chain N).same (φ.relabel j)
      rw [Language.Formula.realize_relabel, Language.Formula.realize_relabel, hleft, hright] at h
      exact h.symm
  }
  exact ⟨{
    toEquiv := _root_.Equiv.ofBijective e ⟨e.injective, hf⟩
    map_fun' := e.toEmbedding.map_fun'
    map_rel' := e.toEmbedding.map_rel'
  }, fun i => f_apply (n := 0) i⟩

/-- If matching tuple types have one-point extensions to either side, the
countable nonempty structures are isomorphic. -/
theorem nonempty_equiv_of_formulaType_backAndForth [Countable A] [Countable B]
    [Nonempty A] [Nonempty B]
    (hzero : SameFormulaType (L := L) (Fin.elim0 : Fin 0 → A) (Fin.elim0 : Fin 0 → B))
    (forth : ∀ {n} {a : Fin n → A} {b : Fin n → B}, SameFormulaType (L := L) a b →
      ∀ x, ∃ y, SameFormulaType (L := L) (Fin.snoc a x) (Fin.snoc b y))
    (back : ∀ {n} {a : Fin n → A} {b : Fin n → B}, SameFormulaType (L := L) a b →
      ∀ y, ∃ x, SameFormulaType (L := L) (Fin.snoc a x) (Fin.snoc b y)) :
    Nonempty (A ≃[L] B) := by
  obtain ⟨e, _⟩ := exists_equiv_of_formulaType_backAndForth hzero forth back
  exact ⟨e⟩

section Categoricity

variable {M N P : Type*} [L.Structure M] [L.Structure N] [L.Structure P]

private noncomputable def quantifyLast {n : ℕ} (φ : L.Formula (Fin (n + 1))) :
    L.Formula (Fin n) :=
  (φ.relabel (Fin.lastCases (Sum.inr ()) Sum.inl)).iExs Unit

private theorem realize_quantifyLast {n : ℕ} (φ : L.Formula (Fin (n + 1)))
    {Q : Type*} [L.Structure Q] (c : Fin n → Q) :
    (quantifyLast φ).Realize c ↔ ∃ z : Q, φ.Realize (Fin.snoc c z) := by
  have reindex (z : Unit → Q) :
      (Sum.elim c z) ∘ Fin.lastCases (Sum.inr ()) Sum.inl = Fin.snoc c (z ()) := by
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k <;> simp
  simp only [quantifyLast, Language.Formula.realize_iExs, Language.Formula.realize_relabel, reindex]
  exact ⟨fun ⟨z, hz⟩ => ⟨z (), hz⟩, fun ⟨z, hz⟩ => ⟨fun _ => z, hz⟩⟩

private theorem exists_snoc_sameFormulaType
    (hMN : M ≅[L] N) (hMP : M ≅[L] P)
    {n : ℕ} {ι : Type*} [Finite ι] (r : ι → Fin (n + 1) → M)
    (cover : ∀ b : Fin (n + 1) → M, ∃ i, SameFormulaType (L := L) (r i) b)
    {a : Fin n → N} {b : Fin n → P}
    (same : SameFormulaType (L := L) a b) (x : N) :
    ∃ y, SameFormulaType (L := L) (Fin.snoc a x) (Fin.snoc b y) := by
  obtain ⟨i, hx⟩ := finite_formula_type_cover_of_elementarilyEquivalent hMN r cover (Fin.snoc a x)
  obtain ⟨φ, hφ⟩ := exists_formula_isolates_in_finite_type_cover r cover (r i)
  let ψ := quantifyLast φ
  have hn : ψ.Realize a := (realize_quantifyLast φ a).mpr
    ⟨x, (isolates_formula_type_of_elementarilyEquivalent hMN hφ _).mpr hx⟩
  obtain ⟨y, hy⟩ := (realize_quantifyLast φ b).mp ((same ψ).mp hn)
  exact ⟨y, hx.symm.trans ((isolates_formula_type_of_elementarilyEquivalent hMP hφ _).mp hy)⟩

/-- In a countable nonempty structure whose realised tuple types admit finite
covers, tuples with the same complete formula type lie in the same automorphism orbit. -/
theorem exists_aut_of_sameFormulaType_of_finite_formula_type_covers
    [Countable M] [Nonempty M]
    (cover : ∀ n : ℕ, ∃ R : Finset (Fin n → M),
      ∀ b : Fin n → M, ∃ a : R, SameFormulaType (L := L) a.val b)
    {k : ℕ} {a b : Fin k → M} (same : SameFormulaType (L := L) a b) :
    ∃ g : FirstOrderAut L M, g • a = b := by
  have extension {n : ℕ} {xs ys : Fin n → M}
      (h : SameFormulaType (L := L) xs ys) (x : M) :
      ∃ y, SameFormulaType (L := L) (Fin.snoc xs x) (Fin.snoc ys y) := by
    obtain ⟨R, hR⟩ := cover (n + 1)
    exact exists_snoc_sameFormulaType (show M ≅[L] M from rfl) (show M ≅[L] M from rfl)
      (fun i : R => i.val) hR h x
  have back {n : ℕ} {xs ys : Fin n → M}
      (h : SameFormulaType (L := L) xs ys) (y : M) :
      ∃ x, SameFormulaType (L := L) (Fin.snoc xs x) (Fin.snoc ys y) := by
    obtain ⟨x, hx⟩ := extension h.symm y
    exact ⟨x, hx.symm⟩
  obtain ⟨e, he⟩ := exists_equiv_of_formulaType_backAndForth same extension back
  exact ⟨FirstOrderAut.ofEquiv e, funext he⟩

/-- For a countable oligomorphic first-order structure, equality of full
finite tuple types implies conjugacy by a structure automorphism. -/
theorem exists_aut_of_sameFormulaType_of_finite_tupleOrbitRepresentatives
    [Countable M] [Nonempty M]
    (hG : ∀ n : ℕ, ∃ R : Finset (Fin n → M), ∀ x : Fin n → M,
      ∃ r ∈ R, ∃ g : FirstOrderAut L M, g • r = x)
    {k : ℕ} {a b : Fin k → M} (same : SameFormulaType (L := L) a b) :
    ∃ g : FirstOrderAut L M, g • a = b := by
  apply exists_aut_of_sameFormulaType_of_finite_formula_type_covers _ same
  intro n
  obtain ⟨R, hR⟩ := hG n
  exact ⟨R, formula_type_cover_of_finset_automorphism_orbit_representatives R hR⟩

/-- Countable models of the same complete theory as a structure with
finitely many realised types at each arity are isomorphic. -/
theorem nonempty_equiv_of_finite_formula_type_covers [Countable N] [Countable P]
    [Nonempty N] [Nonempty P]
    (hMN : M ≅[L] N) (hMP : M ≅[L] P)
    (cover : ∀ n : ℕ, ∃ R : Finset (Fin n → M),
      ∀ b : Fin n → M, ∃ a : R, SameFormulaType (L := L) a.val b) :
    Nonempty (N ≃[L] P) := by
  apply nonempty_equiv_of_formulaType_backAndForth
  · intro φ
    have h : N ≅[L] P := hMN.symm.trans hMP
    let σ : L.Sentence := φ.relabel Fin.elim0
    have he := Language.elementarilyEquivalent_iff.mp h σ
    have hN : (default : Empty → N) ∘ (Fin.elim0 : Fin 0 → Empty) =
        (Fin.elim0 : Fin 0 → N) := funext fun i => Fin.elim0 i
    have hP : (default : Empty → P) ∘ (Fin.elim0 : Fin 0 → Empty) =
        (Fin.elim0 : Fin 0 → P) := funext fun i => Fin.elim0 i
    simpa only [σ, Language.Sentence.Realize, Language.Formula.realize_relabel, hN, hP] using he
  · intro n a b same x
    obtain ⟨R, hR⟩ := cover (n + 1)
    exact exists_snoc_sameFormulaType hMN hMP (fun i : R => i.val) hR same x
  · intro n a b same y
    obtain ⟨R, hR⟩ := cover (n + 1)
    obtain ⟨x, he⟩ := exists_snoc_sameFormulaType hMP hMN (fun i : R => i.val) hR same.symm y
    exact ⟨x, he.symm⟩

/-- The forward implication of Ryll–Nardzewski, expressed using the
pointwise automorphism group's finite tuple-orbit representative sets. -/
theorem categorical_completeTheory_of_finite_tupleOrbitRepresentatives
    (hG : ∀ n : ℕ, ∃ R : Finset (Fin n → M), ∀ x : Fin n → M,
      ∃ r ∈ R, ∃ g : FirstOrderAut L M, g • r = x) :
    Cardinal.Categorical Cardinal.aleph0 (L.completeTheory M) := by
  intro N P hN hP
  have : Countable N := Cardinal.mk_le_aleph0_iff.mp hN.le
  have : Countable P := Cardinal.mk_le_aleph0_iff.mp hP.le
  have : Nonempty N := Cardinal.mk_ne_zero_iff.mp (hN ▸ Cardinal.aleph0_ne_zero)
  have : Nonempty P := Cardinal.mk_ne_zero_iff.mp (hP ▸ Cardinal.aleph0_ne_zero)
  have hMN : M ≅[L] N := Language.elementarilyEquivalent_iff.mpr fun φ =>
    (Language.realize_iff_of_model_completeTheory M N φ).symm
  have hMP : M ≅[L] P := Language.elementarilyEquivalent_iff.mpr fun φ =>
    (Language.realize_iff_of_model_completeTheory M P φ).symm
  exact nonempty_equiv_of_finite_formula_type_covers hMN hMP fun n => by
    obtain ⟨R, hR⟩ := hG n
    exact ⟨R, formula_type_cover_of_finset_automorphism_orbit_representatives R hR⟩

/-- Equivalently, finite quotients by the tuple-orbit relation suffice. -/
theorem categorical_completeTheory_of_finite_tupleOrbitQuotients
    (hG : ∀ n : ℕ, Finite (Quotient (firstOrderTupleOrbit L M n))) :
    Cardinal.Categorical Cardinal.aleph0 (L.completeTheory M) := by
  classical
  apply categorical_completeTheory_of_finite_tupleOrbitRepresentatives
  intro n
  let C := Quotient (firstOrderTupleOrbit L M n)
  let : Finite C := hG n
  let : Fintype C := Fintype.ofFinite C
  let chooseTuple : C → Fin n → M := Quotient.out
  refine ⟨Finset.univ.image chooseTuple, fun a => ?_⟩
  let c : C := Quotient.mk (firstOrderTupleOrbit L M n) a
  have qeq : Quotient.mk (firstOrderTupleOrbit L M n) (chooseTuple c) =
      Quotient.mk (firstOrderTupleOrbit L M n) a := Quotient.out_eq c
  obtain ⟨f, hf⟩ := Quotient.exact qeq
  exact ⟨chooseTuple c, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩,
    FirstOrderAut.ofEquiv f, funext hf⟩

end Categoricity

end SuccessorTree.NonPrecompact
