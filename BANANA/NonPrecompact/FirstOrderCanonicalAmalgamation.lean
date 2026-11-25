import BANANA.NonPrecompact.FirstOrderInvariantTypes
import BANANA.NonPrecompact.FirstOrderOmittingTypes
import Mathlib.ModelTheory.Fraisse

/-!
# Canonical amalgamation and first-order extreme amenability

Choose the amalgam of the parameter-generated substructure with a target,
then embed it in the limit fixing the parameters. Compatibility with
embeddings puts any two images of a source in the same orbit over those
parameters. Finite type covers transfer the resulting definable Ramsey
property to every model of the complete theory.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

universe u v w w' a

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- The finitely generated substructures representing the age of a model. -/
abbrev AgeSubstructure (L : Language.{u, v}) (M : Type w) [L.Structure M] :=
  { S : L.Substructure M // S.FG }

/-- For each fixed first factor, choose amalgams with every second factor in
the age. Every embedding of second factors lifts to an embedding of the
chosen amalgams that commutes with both legs.

Amalgams are represented by finitely generated substructures of the ambient
model. The property makes no disjointness, uniqueness or coherence demand
on the lifted embeddings. -/
def HasCanonicalAgeAmalgamation (L : Language.{u, v}) (M : Type w) [L.Structure M] : Prop :=
  ∀ D : AgeSubstructure L M,
    ∃ (P : AgeSubstructure L M → AgeSubstructure L M)
      (left : ∀ A, D.val ↪[L] (P A).val)
      (right : ∀ A, A.val ↪[L] (P A).val),
      ∀ (A B : AgeSubstructure L M) (f : A.val ↪[L] B.val),
        ∃ e : (P A).val ↪[L] (P B).val,
          e.comp (left A) = left B ∧ e.comp (right A) = (right B).comp f

private def tupleClosure {n : ℕ} (x : Fin n → M) : AgeSubstructure L M :=
  ⟨Language.Substructure.closure L (Set.range x),
    Language.Substructure.fg_closure (Set.finite_range x)⟩

private def tupleInClosure {n : ℕ} (x : Fin n → M) (j : Fin n) :
    (tupleClosure (L := L) x).val :=
  ⟨x j, Language.Substructure.subset_closure ⟨j, rfl⟩⟩

private theorem exists_aut_comp_of_embeddings (homogeneous : L.IsUltrahomogeneous M)
    (S : AgeSubstructure L M) (f g : S.val ↪[L] M) :
    ∃ k : M ≃[L] M, ∀ x : S.val, k (f x) = g x := by
  obtain ⟨e, he⟩ := homogeneous S.val S.property f
  obtain ⟨d, hd⟩ := homogeneous S.val S.property g
  refine ⟨d.comp e.symm, fun x => ?_⟩
  change d (e.symm (f x)) = g x
  rw [he, hd]
  change d (e.symm (e x.val)) = d x.val
  rw [Language.Equiv.symm_apply_apply]

private theorem exists_embedding_on_tupleClosure {n m : ℕ}
    {x : Fin n → M} {y : Fin m → M} (i : Fin n → Fin m)
    (g : M ≃[L] M) (hg : ∀ j, g (x j) = y (i j)) :
    ∃ f : (tupleClosure (L := L) x).val ↪[L] (tupleClosure (L := L) y).val,
      ∀ j, f (tupleInClosure x j) = tupleInClosure y (i j) := by
  let A := tupleClosure (L := L) x
  let B := tupleClosure (L := L) y
  have hle : A.val ≤ B.val.comap g.toEmbedding.toHom := by
    apply Language.Substructure.closure_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Language.Substructure.mem_comap.mpr
      (show g (x j) ∈ B.val by rw [hg]; exact (tupleInClosure (L := L) y (i j)).property)
  let f := (g.toEmbedding.comp A.val.subtype).codRestrict B.val
    (fun x => Language.Substructure.mem_comap.mp (hle x.property))
  exact ⟨f, fun j => Subtype.ext (hg j)⟩

/-- The canonical-amalgamation argument for definable tuple Ramsey in an
ultrahomogeneous structure where matching finite types are conjugate. -/
theorem HasCanonicalAgeAmalgamation.hasDefinableTupleRamsey
    (canonical : HasCanonicalAgeAmalgamation L M) (homogeneous : L.IsUltrahomogeneous M)
    (conjugate : ∀ {n : ℕ} {x y : Fin n → M}, SameFormulaType (L := L) x y →
      ∃ g : M ≃[L] M, ∀ j, g (x j) = y j) :
    HasDefinableTupleRamsey L M := by
  intro l r k c a b p φ
  let A := tupleClosure (L := L) a
  let B := tupleClosure (L := L) b
  let D := tupleClosure (L := L) p
  obtain ⟨P, left, right, compatible⟩ := canonical D
  obtain ⟨h, hh⟩ := homogeneous.extend_embedding
    (D.val.fg_iff_structure_fg.mp D.property) D.val.subtype (left B)
    (h := ⟨(P B).val.subtype⟩)
  let target := h.comp (right B)
  let b' (t : Fin r) := target (tupleInClosure b t)
  have fixed (x : D.val) : h (left B x) = x.val :=
    (congrArg (fun f : D.val ↪[L] M => f x) hh).symm
  obtain ⟨g, hg⟩ := homogeneous B.val B.property target
  have hb' : SameFormulaType (L := L) b b' := by
    intro ψ
    have heq : g ∘ b = b' := funext fun j =>
      (congrArg (fun f : B.val ↪[L] M => f (tupleInClosure b j)) hg).symm
    rw [← heq]
    exact (Language.StrongHomClass.realize_formula g ψ).symm
  refine ⟨b', hb', fun i j hi hj t => ?_⟩
  obtain ⟨gi, hgi⟩ := conjugate hi
  obtain ⟨gj, hgj⟩ := conjugate hj
  obtain ⟨fi, hfi⟩ := exists_embedding_on_tupleClosure i gi hgi
  obtain ⟨fj, hfj⟩ := exists_embedding_on_tupleClosure j gj hgj
  obtain ⟨ei, heiL, heiR⟩ := compatible A B fi
  obtain ⟨ej, hejL, hejR⟩ := compatible A B fj
  obtain ⟨K, hK⟩ := exists_aut_comp_of_embeddings homogeneous (P A) (h.comp ei) (h.comp ej)
  have move (s : Fin l) : K (b' (i s)) = b' (j s) := by
    have lift (f : A.val ↪[L] B.val) (e : (P A).val ↪[L] (P B).val)
        (he : e.comp (right A) = (right B).comp f) (q : Fin l → Fin r)
        (hf : ∀ j, f (tupleInClosure a j) = tupleInClosure b (q j)) :
        h (e (right A (tupleInClosure a s))) = b' (q s) := by
      have eq := congrArg (fun v : A.val ↪[L] (P B).val => v (tupleInClosure a s)) he
      change e (right A (tupleInClosure a s)) = right B (f (tupleInClosure a s)) at eq
      rw [eq, hf]
      rfl
    have hKi := hK (right A (tupleInClosure a s))
    change K (h (ei (right A (tupleInClosure a s)))) =
      h (ej (right A (tupleInClosure a s))) at hKi
    rw [lift fi ei heiR i hfi, lift fj ej hejR j hfj] at hKi
    exact hKi
  have fix (s : Fin k) : K (p s) = p s := by
    have lift (e : (P A).val ↪[L] (P B).val) (he : e.comp (left A) = left B) :
        h (e (left A (tupleInClosure p s))) = p s := by
      have eq := congrArg (fun v : D.val ↪[L] (P B).val => v (tupleInClosure p s)) he
      change e (left A (tupleInClosure p s)) = left B (tupleInClosure p s) at eq
      rw [eq]
      exact fixed (tupleInClosure p s)
    have hKs := hK (left A (tupleInClosure p s))
    change K (h (ei (left A (tupleInClosure p s)))) =
      h (ej (left A (tupleInClosure p s))) at hKs
    rw [lift ei heiL, lift ej hejL] at hKs
    exact hKs
  have heq : K ∘ Sum.elim (b' ∘ i) p = Sum.elim (b' ∘ j) p := by
    funext t
    cases t with
    | inl s => exact move s
    | inr s => exact fix s
  rw [← heq]
  exact (Language.StrongHomClass.realize_formula K (φ t)).symm


/-- Canonical amalgamation yields definable tuple Ramsey for a countable
ultrahomogeneous model with finite covers of its realised finite types. -/
theorem HasCanonicalAgeAmalgamation.hasDefinableTupleRamsey_of_finite_type_covers
    [Countable M] [Nonempty M]
    (canonical : HasCanonicalAgeAmalgamation L M) (homogeneous : L.IsUltrahomogeneous M)
    (cover : ∀ n : ℕ, ∃ R : Finset (Fin n → M),
      ∀ b : Fin n → M, ∃ a : R, SameFormulaType (L := L) a.val b) :
    HasDefinableTupleRamsey L M := by
  refine canonical.hasDefinableTupleRamsey homogeneous (fun h => ?_)
  obtain ⟨g, hg⟩ := exists_aut_of_sameFormulaType_of_finite_formula_type_covers cover h
  exact ⟨g.toEquiv, fun i => congrFun hg i⟩

/-- If an ω-categorical ultrahomogeneous countable model has canonical
amalgamation on its finitely generated age, every type of its complete
theory has an invariant extension over every model of that theory. -/
theorem exists_invariantExtension_of_canonicalAgeAmalgamation
    {L : Language.{0, 0}} [Countable L.Symbols] {M : Type} [L.Structure M]
    [Countable M] [Infinite M]
    (canonical : HasCanonicalAgeAmalgamation L M)
    (homogeneous : L.IsUltrahomogeneous M)
    (categorical : Cardinal.Categorical (Cardinal.aleph0 : Cardinal.{0}) (L.completeTheory M))
    (N : Type w') [L.Structure N] [Nonempty N] (hMN : M ≅[L] N)
    {α : Type a} (p₀ : (L.completeTheory N).CompleteType α) :
    ∃ p : (L.elementaryDiagram N).CompleteType α, IsInvariantType p ∧
      ∀ (φ : L.Formula α), Language.Formula.equivSentence φ ∈ p₀ →
        Language.Formula.equivSentence ((L.lhomWithConstants N).onFormula φ) ∈ p := by
  let cover := finite_formula_type_covers_of_countablyCategorical categorical
  have ramsey : HasDefinableTupleRamsey L M :=
    canonical.hasDefinableTupleRamsey_of_finite_type_covers homogeneous cover
  exact HasDefinableTupleRamsey.exists_invariantExtension
    (ramsey.of_elementarilyEquivalent hMN cover)
    (exists_formula_isolates_of_elementarilyEquivalent_of_finite_type_covers hMN cover) p₀

end SuccessorTree.NonPrecompact
