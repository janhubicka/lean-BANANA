import BANANA.NonPrecompact.FirstOrderPointedRamseyBound

/-!
# Precompactness by generated expansion types

A generated expansion type records an expanded substructure together with the
distinguished copy of the reduct that generates it. The source parametrisation
of the distinguished copy is forgotten, but its range is retained.
-/

namespace SuccessorTree.NonPrecompact.FirstOrderRamseyExpansion

open CategoryTheory FirstOrder
open scoped FirstOrder

universe u v u' v' w

variable {L : Language.{u, v}} {L' : Language.{u', v'}}
  {K : Set (Bundled.{w} L.Structure)} {K' : Set (Bundled.{w} L'.Structure)}

/-- The closure of a distinguished reduct copy, recorded on its own carrier. -/
structure GeneratedPointedDomain (φ : L →ᴸ L') (K' : Set (Bundled.{w} L'.Structure))
    (A : Bundled.{w} L.Structure) where
  domain : K'
  copy : A ↪[L] firstOrderBundledReduct φ domain.val
  generates : Language.Substructure.closure L' (Set.range copy) = ⊤

/-- Two generated pointed domains are identified by an expanded isomorphism
that maps the distinguished reduct copy onto the other. -/
def generatedExpansionSetoid (φ : L →ᴸ L')
    (K' : Set (Bundled.{w} L'.Structure)) (A : Bundled.{w} L.Structure) :
    Setoid (GeneratedPointedDomain φ K' A) where
  r a b := ∃ e : a.domain.val ≃[L'] b.domain.val, e '' Set.range a.copy = Set.range b.copy
  iseqv := by
    refine ⟨fun a => ⟨Language.Equiv.refl L' a.domain.val, Set.image_id _⟩, ?_, ?_⟩
    · rintro a b ⟨e, he⟩
      refine ⟨e.symm, ?_⟩
      rw [← he, Set.image_image]
      change (e.toEquiv.symm ∘ e.toEquiv) '' Set.range a.copy = Set.range a.copy
      rw [Equiv.symm_comp_self, Set.image_id]
    · rintro a b c ⟨e, he⟩ ⟨f, hf⟩
      exact ⟨f.comp e, (Set.image_image f e _).symm.trans (he ▸ hf)⟩

/-- Expansion types counted by the manuscript's precompactness definition. -/
abbrev GeneratedExpansionType (φ : L →ᴸ L')
    (K' : Set (Bundled.{w} L'.Structure)) (A : Bundled.{w} L.Structure) :=
  Quotient (generatedExpansionSetoid φ K' A)

variable (φ : L →ᴸ L')

private theorem exists_generated_domain
    (hHer : Language.Hereditary K')
    (hFinite : ∀ B ∈ K', Finite B)
    {A : Bundled.{w} L.Structure} (B : K')
    (f : A ↪[L] firstOrderBundledReduct φ B.val) :
    ∃ (D : GeneratedPointedDomain φ K' A) (g : D.domain.val ↪[L'] B.val),
      g '' Set.range D.copy = Set.range f := by
  let S := Language.Substructure.closure L' (Set.range f)
  let D : Bundled.{w} L'.Structure := ⟨S, inferInstance⟩
  let : L.Structure S := φ.reduct S
  let copy : A ↪[L] S :=
    { toFun := fun x => ⟨f x, Language.Substructure.subset_closure ⟨x, rfl⟩⟩
      inj' := fun _ _ h => f.injective (congrArg Subtype.val h)
      map_fun' := fun F xs => Subtype.ext (f.map_fun F xs)
      map_rel' := fun R xs => f.map_rel R xs }
  let _ : Finite B.val := hFinite B.val B.property
  have hD : D ∈ K' :=
    hHer B.val B.property ⟨Language.Structure.FG.of_finite, ⟨S.subtype⟩⟩
  have hImage : S.subtype.toHom '' Set.range copy = Set.range f :=
    (Set.range_comp (fun x : S => (x : B.val)) (fun a : A => copy a)).symm
  have hGenerated :
      Language.Substructure.closure L' (Set.range copy) = ⊤ := by
    apply Language.Substructure.map_injective_of_injective
      (f := S.subtype.toHom) S.subtype_injective
    rw [Language.Substructure.map_closure, hImage]
    ext x
    change x ∈ S ↔ ∃ y : S, y ∈ (⊤ : L'.Substructure S) ∧ (y : B.val) = x
    constructor
    · intro hx
      exact ⟨⟨x, hx⟩, Language.Substructure.mem_top _, rfl⟩
    · rintro ⟨y, _, rfl⟩
      exact y.property
  exact ⟨⟨⟨D, hD⟩, copy, hGenerated⟩, S.subtype, hImage⟩

private theorem exists_generated_representatives
    (hHer : Language.Hereditary K')
    (hFinite : ∀ B ∈ K', Finite B)
    (A : Bundled.{w} L.Structure) [Finite (GeneratedExpansionType φ K' A)] :
    ∃ (D : Fin (Nat.card (GeneratedExpansionType φ K' A)) → K')
      (p : ∀ i, A ↪[L] firstOrderBundledReduct φ (D i).val),
      ∀ (B : K') (f : A ↪[L] firstOrderBundledReduct φ B.val),
        ∃ (i : Fin (Nat.card (GeneratedExpansionType φ K' A)))
          (g : (D i).val ↪[L'] B.val), Set.range f = g '' Set.range (p i) := by
  classical
  let T := GeneratedExpansionType φ K' A
  let : Fintype T := Fintype.ofFinite T
  let index : T ≃ Fin (Nat.card T) := Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm
  let rep (i : Fin (Nat.card T)) : GeneratedPointedDomain φ K' A := Quotient.out (index.symm i)
  refine ⟨fun i => (rep i).domain, fun i => (rep i).copy, fun B f => ?_⟩
  obtain ⟨P, g, hg⟩ := exists_generated_domain φ hHer hFinite B f
  let q : T := Quotient.mk _ P
  let i := index q
  have hType : Quotient.mk _ (rep i) = q :=
    (Quotient.out_eq (index.symm i)).trans (index.symm_apply_apply q)
  have hIso : (generatedExpansionSetoid φ K' A).r (rep i) P := Quotient.exact hType
  obtain ⟨e, he⟩ := hIso
  exact ⟨i, g.comp e.toEmbedding, hg.symm.trans ((congrArg (Set.image g) he).symm.trans
    (Set.image_image g e _))⟩

/-- The number of types of expanded closures, with the generating copy
distinguished, bounds the copy Ramsey degree of the reduct. -/
theorem copyRamseyDegreeLE_card_generatedExpansionTypes
    (hK : ∀ B ∈ K, Finite B) (hHer : Language.Hereditary K')
    (hRamsey : FirstOrderEmbeddingRamsey K')
    (hReduct : ∀ B ∈ K', firstOrderBundledReduct φ B ∈ K)
    (hExpansion : ∀ B : K, Nonempty (firstOrderCompatibleExpansions φ K' B.val))
    (A : K) (hPrecompact : Finite (GeneratedExpansionType φ K' A.val)) :
    (firstOrderFiniteCopySystem K hK).CopyRamseyDegreeLE A
      (Nat.card (GeneratedExpansionType φ K' A.val)) := by
  let : Finite (GeneratedExpansionType φ K' A.val) := hPrecompact
  have hFinite : ∀ B ∈ K', Finite B := fun B hB =>
    hK (firstOrderBundledReduct φ B) (hReduct B hB)
  obtain ⟨D, p, hCover⟩ := exists_generated_representatives φ hHer hFinite A.val
  exact FirstOrderPointedRamseyBound.copyRamseyDegreeLE_of_pointed_domains
    φ hK hRamsey hReduct hExpansion A _ (fun B => ⟨D, p, hCover B⟩)

/-- Existence of a hereditary embedding-Ramsey expansion, precompact by
generated expansion types. The degree argument does not need reasonableness
of the expansion, so this predicate allows even non-reasonable expansions. -/
def HasPrecompactGeneratedRamseyExpansion (K : Set (Bundled.{w} L.Structure)) : Prop :=
  ∃ (L' : Language.{u',v'}) (φ : L →ᴸ L') (K' : Set (Bundled.{w} L'.Structure)),
    φ.Injective ∧
    Language.Hereditary K' ∧
    FirstOrderEmbeddingRamsey K' ∧
    (∀ B ∈ K', firstOrderBundledReduct φ B ∈ K) ∧
    (∀ B : K, Nonempty (firstOrderCompatibleExpansions φ K' B.val)) ∧
    ∀ A : K, Finite (GeneratedExpansionType φ K' A.val)

/-- Infinite copy Ramsey degree excludes precompact Ramsey expansions,
including expansions by functions or constants. -/
theorem not_hasPrecompactGeneratedRamseyExpansion
    (hK : ∀ B ∈ K, Finite B) (A : K)
    (hInfinite : ∀ t : ℕ, ¬ (firstOrderFiniteCopySystem K hK).CopyRamseyDegreeLE A t) :
    ¬ HasPrecompactGeneratedRamseyExpansion K := by
  rintro ⟨L', φ, K', -, hHer, hRamsey, hReduct, hExpansion, hPrecompact⟩
  exact hInfinite _ (copyRamseyDegreeLE_card_generatedExpansionTypes
    φ hK hHer hRamsey hReduct hExpansion A (hPrecompact A))

end SuccessorTree.NonPrecompact.FirstOrderRamseyExpansion
