import BANANA.NonPrecompact.EmbeddingCopyRamseyDegree
import BANANA.NonPrecompact.EmbeddingRangeFibres
import BANANA.NonPrecompact.FirstOrderExpansionDegree

/-!
# The embedding-to-copy degree formula for finite first-order structures

Every copy has one embedding for each automorphism of the source.
The same principle applies to the native BANANA and symplectic copy systems.
-/

namespace SuccessorTree.FiniteCopySystem

open Function

variable {S : FiniteCopySystem} {A : S.Obj}

/-- Factorisation through embeddings onto the same copy supplies uniform
fibres of size equal to the number of source automorphisms. -/
noncomputable def UniformEmbeddingFibres.of_factorisation [Finite (S.Emb A A)]
    (cancel : ∀ {B} (g : S.Emb A B),
      Injective (fun f : S.Emb A A => S.compEmb f g))
    (factor : ∀ {B} (f g : S.Emb A B), S.range f = S.range g →
      ∃ e : S.Emb A A, S.compEmb e g = f)
    (full : ∀ f : S.Emb A A, S.range f = S.range (S.idEmb A)) :
    UniformEmbeddingFibres S A (Nat.card (S.ReductAutomorphism A)) where
  index p := by
    let automorphism := selfEmbeddingEquivReductAutomorphism cancel factor full
    letI : Finite (S.ReductAutomorphism A) := Finite.of_equiv _ automorphism
    letI : Fintype (S.ReductAutomorphism A) := Fintype.ofFinite _
    exact (embeddingFibreEquivSelf cancel factor full p).trans
      (automorphism.trans (Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm))
  postcomp_surjective := embeddingFibre_postcomp_surjective factor full

end SuccessorTree.FiniteCopySystem

namespace SuccessorTree.NonPrecompact

open CategoryTheory FirstOrder Function
open scoped FirstOrder

universe u v w

variable {L : Language.{u,v}} {K : Set (Bundled.{w} L.Structure)}
  (hK : ∀ B ∈ K, Finite B)

local notation "S" => firstOrderFiniteCopySystem K hK

/-- Automorphisms in the first-order copy system are ordinary first-order
automorphisms of the source. -/
def firstOrderReductAutomorphismEquiv (A : K) :
    (S).ReductAutomorphism A ≃ (A.val ≃[L] A.val) where
  toFun f := by
    let hom : A.val ↪[L] A.val := f.hom
    let inv : A.val ↪[L] A.val := f.inv
    exact {
      toFun := hom
      invFun := inv
      left_inv := fun x => congrArg (fun e : A.val ↪[L] A.val => e x) f.hom_inv
      right_inv := fun x => congrArg (fun e : A.val ↪[L] A.val => e x) f.inv_hom
      map_fun' := hom.map_fun'
      map_rel' := hom.map_rel' }
  invFun f :=
    ⟨f.toEmbedding, f.symm.toEmbedding,
      Language.Embedding.ext (fun x => f.symm_apply_apply x),
      Language.Embedding.ext (fun x => f.apply_symm_apply x)⟩
  left_inv _ := FiniteCopySystem.ReductAutomorphism.ext
    (Language.Embedding.ext (fun _ => rfl)) (Language.Embedding.ext (fun _ => rfl))
  right_inv _ := DFunLike.ext _ _ (fun _ => rfl)

/-- Each copy in a finite first-order class has as many embeddings onto
it as the source has automorphisms. -/
noncomputable def firstOrderUniformEmbeddingFibres (A : K) :
    (S).UniformEmbeddingFibres A (Nat.card (A.val ≃[L] A.val)) := by
  letI : Finite A.val := hK A.val A.property
  letI : Finite ((S).Emb A A) := by
    change Finite (A.val ↪[L] A.val)
    exact Finite.of_injective (fun f : A.val ↪[L] A.val => (f : A.val → A.val))
      (fun _ _ h => Language.Embedding.ext (congrFun h))
  rw [← Nat.card_congr (firstOrderReductAutomorphismEquiv hK A)]
  apply FiniteCopySystem.UniformEmbeddingFibres.of_factorisation
  · intro B g f₁ f₂ h
    apply Language.Embedding.ext
    intro x
    let g' : A.val ↪[L] B.val := g
    exact g'.injective (congrArg (fun e : A.val ↪[L] B.val => e x) h)
  · intro B f g h
    exact embedding_factor_of_range_subset f g
      (congrArg Subtype.val h).le
  · intro f
    apply Subtype.ext
    let e : A.val ↪[L] A.val := f
    change Set.range e = Set.range (Language.Embedding.refl L A.val)
    exact Set.ext fun x => ⟨fun _ => ⟨x, rfl⟩,
      fun _ => Finite.surjective_of_injective e.injective x⟩

/-- With finite bounds, the ordinary embedding Ramsey degree is the
copy Ramsey degree multiplied by the order of the source automorphism
group. The division form also detects infinite degree. -/
theorem firstOrderEmbeddingRamseyDegreeLE_iff_copyRamseyDegreeLE_div
    (A : K) (t : ℕ) :
    (S).EmbeddingRamseyDegreeLE A t ↔
      (S).CopyRamseyDegreeLE A (t / Nat.card (A.val ≃[L] A.val)) :=
  (firstOrderUniformEmbeddingFibres hK A).embeddingRamseyDegreeLE_iff_copyRamseyDegreeLE_div

/-- If the copy degree exists, the embedding degree is exactly its
product with the number of source automorphisms. -/
theorem isLeast_firstOrderEmbeddingRamseyDegree (A : K) {t : ℕ}
    (h : IsLeast {d : ℕ | (S).CopyRamseyDegreeLE A d} t) :
    IsLeast {d : ℕ | (S).EmbeddingRamseyDegreeLE A d}
      (Nat.card (A.val ≃[L] A.val) * t) :=
  (firstOrderUniformEmbeddingFibres hK A).isLeast_embeddingRamseyDegree h

/-- The two degrees are infinite for the same first-order structures. -/
theorem firstOrderEmbeddingRamseyDegree_infinite_iff (A : K) :
    (∀ t : ℕ, ¬ (S).EmbeddingRamseyDegreeLE A t) ↔
      (∀ t : ℕ, ¬ (S).CopyRamseyDegreeLE A t) :=
  (firstOrderUniformEmbeddingFibres hK A).embeddingRamseyDegree_infinite_iff

end SuccessorTree.NonPrecompact
