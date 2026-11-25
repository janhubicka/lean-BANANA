import Mathlib.ModelTheory.Substructures

/-!
# Hereditary restriction of first-order expansions

An expansion can restrict along a reduct embedding exactly when the
embedding's range is closed under the expanded functions. This holds
automatically when the expansion adds only relations. The restriction
has the prescribed reduct and is unique, so restrictions compose.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder Function
open scoped FirstOrder
open Language.Structure

universe u v u' v' w w' w''

variable {L : Language.{u, v}} {L' : Language.{u', v'}}
  {M : Type w} {N : Type w'} {P : Type w''}
  [L.Structure M] [L.Structure N] [L.Structure P]

/-- The exact compatibility of a reduct embedding with expanded functions
needed to restrict an expansion to its source. Constants are included. -/
def ExpandedRangeClosed [L'.Structure N] (e : M ↪[L] N) : Prop :=
  ∀ (n : ℕ) (f : L'.Functions n) (x : Fin n → M),
    funMap f (e ∘ x) ∈ Set.range e

/-- Closure of an embedding range can equivalently be checked on the carrier
set as a substructure of the expanded target. -/
theorem expandedRangeClosed_iff_exists_substructure [L'.Structure N] (e : M ↪[L] N) :
    ExpandedRangeClosed (L' := L') e ↔
      ∃ S : L'.Substructure N, (S : Set N) = Set.range e := by
  classical
  constructor
  · intro h
    refine ⟨⟨Set.range e, ?_⟩, rfl⟩
    intro n f x hx
    choose a ha using hx
    have eq : (e : M → N) ∘ a = x := funext ha
    rw [← eq]
    exact h n f a
  · rintro ⟨S, hS⟩ n f x
    rw [← hS]
    exact S.fun_mem f (e ∘ x) (fun i => by
      change e (x i) ∈ (S : Set N)
      rw [hS]
      exact ⟨x i, rfl⟩)

/-- A reduct embedding's range is closed when the expansion adds no functions. -/
theorem expandedRangeClosed_of_onFunction_surjective [L'.Structure N]
    (φ : L →ᴸ L') [φ.IsExpansionOn N]
    (hφ : ∀ n, Surjective (fun f : L.Functions n => φ.onFunction f))
    (e : M ↪[L] N) : ExpandedRangeClosed (L' := L') e := by
  intro n g x
  obtain ⟨f, rfl⟩ := hφ n g
  exact ⟨funMap f x, (e.map_fun f x).trans (φ.map_onFunction f (e ∘ x)).symm⟩

/-- In particular any relational expansion of a target restricts along
each reduct embedding into that target. -/
theorem expandedRangeClosed_of_isRelational [L'.Structure N] [L'.IsRelational]
    (e : M ↪[L] N) : ExpandedRangeClosed (L' := L') e := by
  intro n f
  exact isEmptyElim f

/-- Pull back every relation and every function of a compatible expansion. -/
@[instance_reducible]
noncomputable def restrictFirstOrderExpansion [L'.Structure N] (e : M ↪[L] N)
    (h : ExpandedRangeClosed (L' := L') e) : L'.Structure M where
  funMap f x := (h _ f x).choose
  RelMap r x := RelMap r (e ∘ x)

/-- The original embedding lifts to an embedding for the restricted structure. -/
noncomputable def restrictFirstOrderExpansion_embedding [L'.Structure N] (e : M ↪[L] N)
    (h : ExpandedRangeClosed (L' := L') e) :
    let _ : L'.Structure M := restrictFirstOrderExpansion e h
    M ↪[L'] N := by
  let _ : L'.Structure M := restrictFirstOrderExpansion e h
  exact { toEmbedding := e.toEmbedding
          map_fun' := fun {n} f x => (h n f x).choose_spec
          map_rel' := fun {_} _ _ => Iff.rfl }

/-- The restricted structure still expands the source, with the prescribed reduct. -/
theorem restrictFirstOrderExpansion_isExpansionOn [L'.Structure N]
    (φ : L →ᴸ L') [φ.IsExpansionOn N] (e : M ↪[L] N) (h : ExpandedRangeClosed (L' := L') e) :
    let _ : L'.Structure M := restrictFirstOrderExpansion e h
    φ.IsExpansionOn M := by
  let _ : L'.Structure M := restrictFirstOrderExpansion e h
  constructor
  · intro n f x
    apply e.injective
    exact (h _ (φ.onFunction f) x).choose_spec.trans
      ((φ.map_onFunction f (e ∘ x)).trans (e.map_fun f x).symm)
  · intro n r x
    change RelMap (φ.onRelation r) (e ∘ x) = RelMap r x
    rw [φ.map_onRelation]
    exact propext (e.map_rel r x)

/-- The closure condition is necessary for a lift to an expanded embedding. -/
theorem expandedRangeClosed_of_expandedEmbedding [L'.Structure N] [L'.Structure M]
    (e : M ↪[L] N) (g : M ↪[L'] N) (hg : ∀ x, g x = e x) :
    ExpandedRangeClosed (L' := L') e := by
  intro n f x
  refine ⟨funMap f x, ?_⟩
  have hcomp : (g : M → N) ∘ x = (e : M → N) ∘ x := funext fun i => hg (x i)
  rw [← hg, g.map_fun, hcomp]

/-- Restricting is exactly possible when the expanded operations preserve
the image; when possible, the restriction retains the original source
structure as its reduct. -/
theorem expandedRangeClosed_iff_exists_restriction [L'.Structure N]
    (φ : L →ᴸ L') [φ.IsExpansionOn N] (e : M ↪[L] N) :
    ExpandedRangeClosed (L' := L') e ↔
      ∃ (S : L'.Structure M) (_ : @Language.LHom.IsExpansionOn L L' φ M _ S)
        (g : @Language.Embedding L' M N S _), ∀ x, (@Language.Embedding.toEmbedding L' M N S _ g) x = e x := by
  constructor
  · intro h
    exact ⟨restrictFirstOrderExpansion e h, restrictFirstOrderExpansion_isExpansionOn φ e h,
      restrictFirstOrderExpansion_embedding e h, fun _ => rfl⟩
  · rintro ⟨S, _, g, hg⟩
    let _ : L'.Structure M := S
    exact (expandedRangeClosed_of_expandedEmbedding (L' := L') e g (fun x => hg x))

/-- A fixed injective map into an expanded structure induces at most one
source structure for which the map is an expanded embedding. -/
theorem firstOrderExpansion_eq_of_embeddings [SN : L'.Structure N] {S T : L'.Structure M}
    (g : @Language.Embedding L' M N S SN) (h : @Language.Embedding L' M N T SN)
    (he : ∀ x, (@Language.Embedding.toEmbedding L' M N S SN g) x =
      (@Language.Embedding.toEmbedding L' M N T SN h) x) : S = T := by
  let ge := @Language.Embedding.toEmbedding L' M N S SN g
  let hee := @Language.Embedding.toEmbedding L' M N T SN h
  have he' : (ge : M → N) = hee := funext he
  apply Language.Structure.ext
  · funext n f x
    apply ge.injective
    change ge (@funMap L' M S n f x) = ge (@funMap L' M T n f x)
    rw [show ge (@funMap L' M T n f x) = hee (@funMap L' M T n f x) from he _]
    exact (@Language.Embedding.map_fun' L' M N S SN g n f x).trans
      ((congrArg (fun k : M → N => funMap f (k ∘ x)) he').trans
        (@Language.Embedding.map_fun' L' M N T SN h n f x).symm)
  · funext n r x
    exact propext <| (@Language.Embedding.map_rel' L' M N S SN g n r x).symm.trans
      ((congrArg (fun k : M → N => RelMap r (k ∘ x)) he').to_iff.trans
        (@Language.Embedding.map_rel' L' M N T SN h n r x))

/-- Restricting along the identity does not change the expansion. -/
theorem restrictFirstOrderExpansion_refl [S : L'.Structure M]
    (h : ExpandedRangeClosed (L' := L') (Language.Embedding.refl L M)) :
    restrictFirstOrderExpansion (Language.Embedding.refl L M) h = S :=
  firstOrderExpansion_eq_of_embeddings (restrictFirstOrderExpansion_embedding _ h)
    (Language.Embedding.refl L' M) fun _ => rfl

/-- Pulling back along a composite agrees with the iterated pullback. -/
theorem restrictFirstOrderExpansion_comp [SP : L'.Structure P]
    (e : M ↪[L] N) (g : N ↪[L] P) (hg : ExpandedRangeClosed (L' := L') g)
    (he : @ExpandedRangeClosed L L' M N _ _ (restrictFirstOrderExpansion g hg) e)
    (hcomp : ExpandedRangeClosed (L' := L') (g.comp e)) :
    restrictFirstOrderExpansion (g.comp e) hcomp =
      @restrictFirstOrderExpansion L L' M N _ _ (restrictFirstOrderExpansion g hg) e he := by
  let SN : L'.Structure N := restrictFirstOrderExpansion g hg
  let SM : L'.Structure M := @restrictFirstOrderExpansion L L' M N _ _ SN e he
  let e' : @Language.Embedding L' M N SM SN :=
    @restrictFirstOrderExpansion_embedding L L' M N _ _ SN e he
  let g' : @Language.Embedding L' N P SN SP := restrictFirstOrderExpansion_embedding g hg
  exact firstOrderExpansion_eq_of_embeddings
    (restrictFirstOrderExpansion_embedding (g.comp e) hcomp)
    (@Language.Embedding.comp L' M N SM SN P SP g' e') fun _ => rfl

end SuccessorTree.NonPrecompact
