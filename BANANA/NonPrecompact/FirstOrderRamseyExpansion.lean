import BANANA.NonPrecompact.FirstOrderExpansionDegree
import BANANA.NonPrecompact.FirstOrderFiniteExpansionTypes
import BANANA.NonPrecompact.FirstOrderHereditaryExpansionRestriction

/-!
# Copy Ramsey degrees from hereditary first-order expansions

The embedding Ramsey property of a class of expanded structures
gives the copy Ramsey degree bound on the reduct class when expansion
restricts along every reduct embedding. Heredity supplies these
restrictions when no functions are added, and precompactness counts
isomorphism types on the fixed reduct.
-/

namespace SuccessorTree.NonPrecompact

open CategoryTheory FirstOrder Function
open scoped FirstOrder

universe u v u' v' w

variable {L : Language.{u, v}} {L' : Language.{u', v'}}

private abbrev Class (L : Language.{u, v}) := Set (Bundled.{w} L.Structure)

/-- The embedding Ramsey property for an ordinary class of structures. -/
def FirstOrderEmbeddingRamsey (K : Class.{u,v,w} L) : Prop :=
  ∀ (A B : K) (r : ℕ), 0 < r → ∃ C : K,
    ∀ colouring : (A.val ↪[L] C.val) → Fin r,
      ∃ g : B.val ↪[L] C.val, ∀ e₁ e₂ : A.val ↪[L] B.val,
        colouring (g.comp e₁) = colouring (g.comp e₂)

/-- The reduct of a bundled first-order structure, on the same carrier. -/
abbrev firstOrderBundledReduct (φ : L →ᴸ L') (A : Bundled.{w} L'.Structure) :
    Bundled.{w} L.Structure :=
  ⟨A, φ.reduct A⟩

/-- The members of the expanded class with the prescribed labelled reduct. -/
def firstOrderCompatibleExpansions (φ : L →ᴸ L') (K' : Class.{u',v',w} L')
    (A : Bundled.{w} L.Structure) : Set (L'.Structure A) :=
  {S | Bundled.mk A S ∈ K' ∧ @Language.LHom.IsExpansionOn L L' φ A A.str S}

namespace FirstOrderRamseyExpansion

variable {K : Class.{u,v,w} L} {K' : Class.{u',v',w} L'} (φ : L →ᴸ L')

private abbrev Exp (A : K) := firstOrderCompatibleExpansions φ K' A.val

private abbrev pack {A : K} (a : Exp (K' := K') φ A) : K' :=
  ⟨Bundled.mk A.val a.val, a.property.1⟩

private def reductEmbedding {A B : K} {a : Exp (K' := K') φ A} {b : Exp (K' := K') φ B}
    (g : ((pack φ a).val ↪[L'] (pack φ b).val)) : A.val ↪[L] B.val := by
  letI : L'.Structure A.val := a.val
  letI : L'.Structure B.val := b.val
  letI : φ.IsExpansionOn A.val := a.property.2
  letI : φ.IsExpansionOn B.val := b.property.2
  exact {
    toEmbedding := g.toEmbedding
    map_fun' := fun f x => by simpa only [φ.map_onFunction] using g.map_fun' (φ.onFunction f) x
    map_rel' := fun r x => by simpa only [φ.map_onRelation] using g.map_rel' (φ.onRelation r) x }

section Restriction

variable (hK : ∀ B ∈ K, Finite B) (hHer : Language.Hereditary K')
variable (hClosure : ∀ {A B : K} (e : A.val ↪[L] B.val)
  (b : firstOrderCompatibleExpansions φ K' B.val),
  @ExpandedRangeClosed L L' A.val B.val A.val.str B.val.str b.val e)

private noncomputable def restrict {A B : K} (e : A.val ↪[L] B.val)
    (b : Exp (K' := K') φ B) : Exp (K' := K') φ A := by
  letI : Finite A.val := hK A.val A.property
  letI : L'.Structure B.val := b.val
  letI : φ.IsExpansionOn B.val := b.property.2
  let h : ExpandedRangeClosed (L' := L') e := hClosure e b
  exact ⟨restrictFirstOrderExpansion e h, restrictFirstOrderExpansion_mem_of_hereditary
    hHer b.property.1 e h, restrictFirstOrderExpansion_isExpansionOn φ e h⟩

private noncomputable def restrictEmbedding {A B : K} (e : A.val ↪[L] B.val)
    (b : Exp (K' := K') φ B) :
    (pack φ (restrict φ hK hHer hClosure e b)).val ↪[L'] (pack φ b).val :=
  @restrictFirstOrderExpansion_embedding L L' A.val B.val A.val.str B.val.str b.val e
    (hClosure e b)

private theorem restrict_eq_iff_exists_embedding {A B : K} (e : A.val ↪[L] B.val)
    (a : Exp (K' := K') φ A) (b : Exp (K' := K') φ B) :
    restrict φ hK hHer hClosure e b = a ↔
      ∃ g : (pack φ a).val ↪[L'] (pack φ b).val, reductEmbedding φ g = e := by
  constructor
  · rintro rfl
    exact ⟨restrictEmbedding φ hK hHer hClosure e b, Language.Embedding.ext (fun _ => rfl)⟩
  · rintro ⟨g, hg⟩
    apply Subtype.ext
    exact @firstOrderExpansion_eq_of_embeddings L' A.val B.val b.val _ _
      (restrictEmbedding φ hK hHer hClosure e b) g
      (fun x => (congrArg (fun f : A.val ↪[L] B.val => f x) hg).symm)

private theorem restrict_id {A : K} (a : Exp (K' := K') φ A) :
    restrict φ hK hHer hClosure (Language.Embedding.refl L A.val) a = a :=
  (restrict_eq_iff_exists_embedding φ hK hHer hClosure _ a a).mpr
    ⟨Language.Embedding.refl L' (pack φ a).val, Language.Embedding.ext (fun _ => rfl)⟩

private theorem restrict_comp {A B C : K} (f : A.val ↪[L] B.val)
    (g : B.val ↪[L] C.val) (c : Exp (K' := K') φ C) :
    restrict φ hK hHer hClosure (g.comp f) c =
      restrict φ hK hHer hClosure f (restrict φ hK hHer hClosure g c) :=
  (restrict_eq_iff_exists_embedding φ hK hHer hClosure _ _ c).mpr
    ⟨(restrictEmbedding φ hK hHer hClosure g c).comp (restrictEmbedding φ hK hHer hClosure f _),
      Language.Embedding.ext (fun _ => rfl)⟩

private noncomputable def expandedEmbeddingEquiv {A B : K} (a : Exp (K' := K') φ A)
    (b : Exp (K' := K') φ B) :
    ((pack φ a).val ↪[L'] (pack φ b).val) ≃
      {f : A.val ↪[L] B.val // restrict φ hK hHer hClosure f b = a} where
  toFun g := ⟨reductEmbedding φ g,
    (restrict_eq_iff_exists_embedding φ hK hHer hClosure _ a b).mpr ⟨g, rfl⟩⟩
  invFun f := ((restrict_eq_iff_exists_embedding φ hK hHer hClosure f.1 a b).mp f.2).choose
  left_inv g := by
    let f := reductEmbedding φ g
    have h : ∃ j : (pack φ a).val ↪[L'] (pack φ b).val, reductEmbedding φ j = f :=
      (restrict_eq_iff_exists_embedding φ hK hHer hClosure f a b).mp
        ((restrict_eq_iff_exists_embedding φ hK hHer hClosure f a b).mpr ⟨g, rfl⟩)
    exact Language.Embedding.ext fun x =>
      congrArg (fun j : A.val ↪[L] B.val => j x) h.choose_spec
  right_inv f := Subtype.ext
    ((restrict_eq_iff_exists_embedding φ hK hHer hClosure f.1 a b).mp f.2).choose_spec

private theorem ramsey_of_expandedClass (hRamsey : FirstOrderEmbeddingRamsey K')
    (hReduct : ∀ C ∈ K', firstOrderBundledReduct φ C ∈ K)
    {A B : K} (a : Exp (K' := K') φ A) (b : Exp (K' := K') φ B) (r : ℕ) (hr : 0 < r) :
    ∃ (C : K) (c : Exp (K' := K') φ C),
      ∀ colouring : {f : A.val ↪[L] C.val // restrict φ hK hHer hClosure f c = a} → Fin r,
        ∃ g : {g : B.val ↪[L] C.val // restrict φ hK hHer hClosure g c = b},
          ∀ e₁ e₂ : {e : A.val ↪[L] B.val // restrict φ hK hHer hClosure e b = a},
            colouring ⟨g.1.comp e₁.1, by rw [restrict_comp, g.2, e₁.2]⟩ =
              colouring ⟨g.1.comp e₂.1, by rw [restrict_comp, g.2, e₂.2]⟩ := by
  obtain ⟨C', hC'⟩ := hRamsey (pack φ a) (pack φ b) r hr
  let C : K := ⟨firstOrderBundledReduct φ C'.val, hReduct C'.val C'.property⟩
  let c : Exp (K' := K') φ C :=
    ⟨C'.val.str, C'.property, Language.LHom.isExpansionOn_reduct φ C'.val⟩
  refine ⟨C, c, fun colouring => ?_⟩
  let eac := expandedEmbeddingEquiv φ hK hHer hClosure a c
  let eab := expandedEmbeddingEquiv φ hK hHer hClosure a b
  let ebc := expandedEmbeddingEquiv φ hK hHer hClosure b c
  obtain ⟨g, hg⟩ := hC' (fun f => colouring (eac f))
  refine ⟨ebc g, fun e₁ e₂ => ?_⟩
  have he (e : {e : A.val ↪[L] B.val // restrict φ hK hHer hClosure e b = a}) :
      eac (g.comp (eab.symm e)) =
        ⟨(ebc g).1.comp e.1, by rw [restrict_comp, (ebc g).2, e.2]⟩ := by
    apply Subtype.ext
    have heu := congrArg Subtype.val (eab.apply_symm_apply e)
    change reductEmbedding φ (a := a) (b := c) (g.comp (eab.symm e)) =
      (reductEmbedding φ (a := b) (b := c) g).comp e.1
    rw [← heu]
    exact Language.Embedding.ext (fun _ => rfl)
  simpa only [he] using hg (eab.symm e₁) (eab.symm e₂)

/-- A precompact hereditary class with all restrictions gives a Ramsey expansion
of the copy system of its reduct class. The Ramsey property uses ordinary
first-order embeddings in the expanded class. -/
noncomputable def toRamseyExpansion
    (hRamsey : FirstOrderEmbeddingRamsey K')
    (hReduct : ∀ C ∈ K', firstOrderBundledReduct φ C ∈ K)
    (hExpansion : ∀ A : K, Nonempty (firstOrderCompatibleExpansions φ K' A.val))
    (hPrecompact : ∀ A : K, Finite
      (Quotient (firstOrderStructureIsomorphismSetoid (firstOrderCompatibleExpansions φ K' A.val)))) :
    RamseyExpansion (firstOrderFiniteCopySystem K hK) where
  Exp A := ↥(Exp (K' := K') φ A)
  expFintype A := by
    letI : Finite A.val := hK A.val A.property
    letI := hPrecompact A
    letI := finite_firstOrderStructures_of_finite_isomorphism_types
      (firstOrderCompatibleExpansions φ K' A.val)
    exact Fintype.ofFinite _
  expDecidableEq _ := Classical.decEq _
  expNonempty := hExpansion
  restrict := restrict φ hK hHer hClosure
  restrict_id := restrict_id φ hK hHer hClosure
  restrict_comp := restrict_comp φ hK hHer hClosure
  ramsey := ramsey_of_expandedClass φ hK hHer hClosure hRamsey hReduct

private theorem restrict_automorphism_iff_isomorphic {A : K}
    (a b : Exp (K' := K') φ A) :
    (∃ u : (firstOrderFiniteCopySystem K hK).ReductAutomorphism A,
      restrict φ hK hHer hClosure u.hom b = a) ↔
      Nonempty ((pack φ a).val ≃[L'] (pack φ b).val) := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨g, hg⟩ := (restrict_eq_iff_exists_embedding φ hK hHer hClosure _ a b).mp hu
    let hom : A.val ↪[L] A.val := u.hom
    let inv : A.val ↪[L] A.val := u.inv
    have hg_apply (x : A.val) : g x = hom x :=
      congrArg (fun (f : A.val ↪[L] A.val) => f x) hg
    have hleft (x : A.val) : inv (hom x) = x :=
      congrArg (fun (f : A.val ↪[L] A.val) => f x) u.hom_inv
    have hright (x : A.val) : hom (inv x) = x :=
      congrArg (fun (f : A.val ↪[L] A.val) => f x) u.inv_hom
    exact ⟨{ toEquiv := ⟨g, inv, fun x => (congrArg inv (hg_apply x)).trans (hleft x),
                  fun x => (hg_apply (inv x)).trans (hright x)⟩
             map_fun' := g.map_fun'
             map_rel' := g.map_rel' }⟩
  · rintro ⟨g⟩
    let u : (firstOrderFiniteCopySystem K hK).ReductAutomorphism A := {
      hom := reductEmbedding φ g.toEmbedding
      inv := reductEmbedding φ g.symm.toEmbedding
      hom_inv := Language.Embedding.ext (fun x => g.symm_apply_apply x)
      inv_hom := Language.Embedding.ext (fun x => g.apply_symm_apply x) }
    exact ⟨u, (restrict_eq_iff_exists_embedding φ hK hHer hClosure _ a b).mpr ⟨g.toEmbedding, rfl⟩⟩

private noncomputable def expansionTypesEquiv
    (hRamsey : FirstOrderEmbeddingRamsey K')
    (hReduct : ∀ C ∈ K', firstOrderBundledReduct φ C ∈ K)
    (hExpansion : ∀ A : K, Nonempty (firstOrderCompatibleExpansions φ K' A.val))
    (hPrecompact : ∀ A : K, Finite
      (Quotient (firstOrderStructureIsomorphismSetoid (firstOrderCompatibleExpansions φ K' A.val))))
    (A : K) :
    Quotient (RamseyExpansion.expansionIsomorphismSetoid
      (toRamseyExpansion φ hK hHer hClosure hRamsey hReduct hExpansion hPrecompact) A) ≃
      Quotient (firstOrderStructureIsomorphismSetoid (firstOrderCompatibleExpansions φ K' A.val)) := by
  apply Quotient.congrRight
  intro a b
  exact restrict_automorphism_iff_isomorphic φ hK hHer hClosure a b

end Restriction

/-- If all reduct embeddings into a member of the hereditary, precompact
expanded class have ranges closed under the expanded functions, the number
of actual expansion isomorphism types bounds the ordinary copy Ramsey degree. -/
theorem copyRamseyDegreeLE_card_expansionTypes_of_closed_ranges
    (hK : ∀ B ∈ K, Finite B) (hHer : Language.Hereditary K')
    (hClosure : ∀ {A B : K} (e : A.val ↪[L] B.val)
      (b : firstOrderCompatibleExpansions φ K' B.val),
      @ExpandedRangeClosed L L' A.val B.val A.val.str B.val.str b.val e)
    (hRamsey : FirstOrderEmbeddingRamsey K')
    (hReduct : ∀ C ∈ K', firstOrderBundledReduct φ C ∈ K)
    (hExpansion : ∀ A : K, Nonempty (firstOrderCompatibleExpansions φ K' A.val))
    (hPrecompact : ∀ A : K, Finite
      (Quotient (firstOrderStructureIsomorphismSetoid (firstOrderCompatibleExpansions φ K' A.val))))
    (A : K) :
    (firstOrderFiniteCopySystem K hK).CopyRamseyDegreeLE A
      (Nat.card (Quotient (firstOrderStructureIsomorphismSetoid
        (firstOrderCompatibleExpansions φ K' A.val)))) := by
  rw [← Nat.card_congr
    (expansionTypesEquiv φ hK hHer hClosure hRamsey hReduct hExpansion hPrecompact A)]
  exact firstOrderCopyRamseyDegreeLE_card_expansionIsomorphismTypes
    (toRamseyExpansion φ hK hHer hClosure hRamsey hReduct hExpansion hPrecompact) A

/-- For a precompact hereditary embedding Ramsey expansion which adds no
functions, the copy Ramsey degree is bounded by the number of expansion
isomorphism types. -/
theorem copyRamseyDegreeLE_card_expansionTypes_of_relational
    (hK : ∀ B ∈ K, Finite B) (hHer : Language.Hereditary K')
    (hFunctions : ∀ n, Surjective (fun f : L.Functions n => φ.onFunction f))
    (hRamsey : FirstOrderEmbeddingRamsey K')
    (hReduct : ∀ C ∈ K', firstOrderBundledReduct φ C ∈ K)
    (hExpansion : ∀ A : K, Nonempty (firstOrderCompatibleExpansions φ K' A.val))
    (hPrecompact : ∀ A : K, Finite
      (Quotient (firstOrderStructureIsomorphismSetoid (firstOrderCompatibleExpansions φ K' A.val))))
    (A : K) :
    (firstOrderFiniteCopySystem K hK).CopyRamseyDegreeLE A
      (Nat.card (Quotient (firstOrderStructureIsomorphismSetoid
        (firstOrderCompatibleExpansions φ K' A.val)))) := by
  apply copyRamseyDegreeLE_card_expansionTypes_of_closed_ranges φ hK hHer _ hRamsey
    hReduct hExpansion hPrecompact A
  intro A B e b
  let : L'.Structure B.val := b.val
  let : φ.IsExpansionOn B.val := b.property.2
  exact expandedRangeClosed_of_onFunction_surjective φ hFunctions e

end FirstOrderRamseyExpansion

end SuccessorTree.NonPrecompact
