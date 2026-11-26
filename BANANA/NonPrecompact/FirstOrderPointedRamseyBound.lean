import BANANA.NonPrecompact.FirstOrderRamseyExpansion

/-!
# Copy degree bounds from pointed expanded substructures

A finite list of expanded structures, each carrying a distinguished reduct
copy of the source, suffices for a copy degree bound if their images cover the
copies of the source in each expanded target. This permits the distinguished
copy to generate a strictly larger substructure in the expanded language.
-/

namespace SuccessorTree.NonPrecompact.FirstOrderPointedRamseyBound

open CategoryTheory FirstOrder
open scoped FirstOrder

universe u v u' v' w
variable {L : Language.{u, v}} {L' : Language.{u', v'}}
variable {K : Set (Bundled.{w} L.Structure)} {K' : Set (Bundled.{w} L'.Structure)}

/-- An expanded embedding acts on reduct structures by the same function. -/
def reductEmbedding (φ : L →ᴸ L') {B C : Bundled.{w} L'.Structure}
    (g : B ↪[L'] C) :
    firstOrderBundledReduct φ B ↪[L] firstOrderBundledReduct φ C where
  toEmbedding := g.toEmbedding
  map_fun' := fun f x => g.map_fun' (φ.onFunction f) x
  map_rel' := fun R x => g.map_rel' (φ.onRelation R) x

private theorem simultaneous_ramsey {I : Type*} (D : I → K')
    (types : Finset I) (B : K') (hRamsey : FirstOrderEmbeddingRamsey K')
    (r : ℕ) (hr : 0 < r) :
    ∃ C : K', ∀ colour : ∀ i, ((D i).val ↪[L'] C.val) → Fin r,
      ∃ g : B.val ↪[L'] C.val, ∀ i ∈ types,
        ∀ e₁ e₂ : (D i).val ↪[L'] B.val, colour i (g.comp e₁) = colour i (g.comp e₂) := by
  classical
  induction types using Finset.induction_on with
  | empty =>
      exact ⟨B, fun _ => ⟨Language.Embedding.refl L' B.val, by simp⟩⟩
  | @insert i types _ ih =>
      obtain ⟨C₀, hC₀⟩ := ih
      obtain ⟨C, hC⟩ := hRamsey (D i) C₀ r hr
      refine ⟨C, fun colour => ?_⟩
      obtain ⟨h, hh⟩ := hC (colour i)
      obtain ⟨g, hg⟩ := hC₀ fun j e => colour j (h.comp e)
      refine ⟨h.comp g, fun j hj e₁ e₂ => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [Language.Embedding.comp_assoc] using hh (g.comp e₁) (g.comp e₂)
      · simpa only [Language.Embedding.comp_assoc] using hg j hj e₁ e₂

/-- A family of `t` pointed expanded domains covering the source copies in
each expanded target gives a reduct copy Ramsey degree bound of `t`.
The representatives can depend on the expanded target. -/
theorem copyRamseyDegreeLE_of_pointed_domains
    (φ : L →ᴸ L') (hK : ∀ B ∈ K, Finite B) (hRamsey : FirstOrderEmbeddingRamsey K')
    (hReduct : ∀ C ∈ K', firstOrderBundledReduct φ C ∈ K)
    (hExpansion : ∀ A : K, Nonempty (firstOrderCompatibleExpansions φ K' A.val))
    (A : K) (t : ℕ)
    (hCover : ∀ B' : K', ∃ (D : Fin t → K')
      (p : ∀ i, A.val ↪[L] firstOrderBundledReduct φ (D i).val),
        ∀ f : A.val ↪[L] firstOrderBundledReduct φ B'.val,
          ∃ (i : Fin t) (g : (D i).val ↪[L'] B'.val), Set.range f = g '' Set.range (p i)) :
    (firstOrderFiniteCopySystem K hK).CopyRamseyDegreeLE A t := by
  classical
  let S := firstOrderFiniteCopySystem K hK
  intro B r hr
  obtain ⟨b⟩ := hExpansion B
  let B' : K' := ⟨Bundled.mk B.val b.val, b.property.1⟩
  let iB : B.val ↪[L] firstOrderBundledReduct φ B'.val :=
    { toEmbedding := Function.Embedding.refl _
      map_fun' := fun f x => (@Language.LHom.IsExpansionOn.map_onFunction L L' φ B.val
        B.val.str b.val b.property.2 _ f x).symm
      map_rel' := fun R x => iff_of_eq (@Language.LHom.IsExpansionOn.map_onRelation L L' φ B.val
        B.val.str b.val b.property.2 _ R x) }
  obtain ⟨D, p, hB⟩ := hCover B'
  obtain ⟨C', hC'⟩ := simultaneous_ramsey D Finset.univ B' hRamsey r hr
  let C : K := ⟨firstOrderBundledReduct φ C'.val, hReduct C'.val C'.property⟩
  refine ⟨C, fun colouring => ?_⟩
  let colour (i : Fin t) (e : (D i).val ↪[L'] C'.val) : Fin r :=
    colouring (S.range ((reductEmbedding φ e).comp (p i)))
  obtain ⟨g, hg⟩ := hC' colour
  let f : S.Emb B C := (reductEmbedding φ g).comp iB
  let colourByType (i : Fin t) : Fin r :=
    if h : Nonempty ((D i).val ↪[L'] B'.val) then
      colour i (g.comp (Classical.choice h))
    else
      ⟨0, hr⟩
  refine ⟨f, ?_⟩
  have hsubset : S.coloursInside colouring f ⊆ Finset.univ.image colourByType := by
    intro c hc
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨a, ha⟩ := S.range_surjective q
    obtain ⟨i, e, he⟩ := hB (iB.comp a)
    have hmatch : S.mapCopy f q =
        S.range (A := A) (B := C) ((reductEmbedding φ (g.comp e)).comp (p i)) := by
      calc
        _ = S.mapCopy f (S.range a) := congrArg (S.mapCopy f) ha.symm
        _ = S.range (S.compEmb a f) := (S.range_comp a f).symm
        _ = _ := by
          apply Subtype.ext
          change Set.range (f.comp a) = Set.range ((reductEmbedding φ (g.comp e)).comp (p i))
          calc
            _ = g '' Set.range (iB.comp a) := Set.range_comp _ _
            _ = g '' (e '' Set.range (p i)) := congrArg (Set.image g) he
            _ = _ := (Set.image_image g e _).trans (Set.range_comp _ _).symm
    have h : Nonempty ((D i).val ↪[L'] B'.val) := ⟨e⟩
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    calc
      _ = colour i (g.comp (Classical.choice h)) := dite_eq_left h
      _ = colour i (g.comp e) := hg i (Finset.mem_univ _) (Classical.choice h) e
      _ = _ := congrArg colouring hmatch.symm
  exact (Finset.card_le_card hsubset).trans (Finset.card_image_le.trans (by simp))

end SuccessorTree.NonPrecompact.FirstOrderPointedRamseyBound
