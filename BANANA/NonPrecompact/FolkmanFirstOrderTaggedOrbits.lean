import BANANA.NonPrecompact.FolkmanFirstOrderDecoding
import BANANA.NonPrecompact.FiniteInvariantRepresentatives

/-!
# Finite mixed-sort tuple orbits of the Folkman limit

The encoded product tuple and the list of actual sorts together determine
the orbit of a mixed-sort tuple. The sort list distinguishes the two
named zeros. An automorphism of the product decomposes into pairing-
preserving ring automorphisms of the two decoded sorts.
-/

namespace SuccessorTree.NonPrecompact.FolkmanDecoding

open FirstOrder CategoryTheory
open scoped FirstOrder

variable (M : Bundled.{0} folkmanLanguage.Structure)
variable (hD : FactorsThroughPairedProducts M)

/-- An ordered tuple in the disjoint union of the decoded sorts. -/
abbrev TaggedTuple (n : ℕ) : Type :=
  letI := productRing M hD
  Fin n → leftSort M hD ⊕ rightSort M hD

private abbrev sortTag (v : leftSort M hD ⊕ rightSort M hD) : Bool :=
  match v with
  | .inl _ => false
  | .inr _ => true

private def productValue (v : leftSort M hD ⊕ rightSort M hD) :
    leftSort M hD × rightSort M hD := by
  letI := productRing M hD
  exact match v with
    | .inl x => (x, 0)
    | .inr y => (0, y)

/-- Two tagged tuples are conjugate if one pair of ring automorphisms
preserving the cross-pairing carries each entry to its match. -/
def TaggedOrbit {n : ℕ} (s t : TaggedTuple M hD n) : Prop :=
  letI := productRing M hD
  ∃ (el : leftSort M hD ≃+* leftSort M hD)
    (er : rightSort M hD ≃+* rightSort M hD),
    (∀ x y, pairing M hD (el x) (er y) = pairing M hD x y) ∧
    ∀ i, Sum.map el er (s i) = t i

/-- A complete finite invariant for encoded tuples gives finite representatives
for the pairing-preserving automorphism orbits of decoded mixed-sort tuples. -/
theorem exists_finite_tagged_tuple_orbit_representatives_of_invariant
    {n : ℕ} {C : Type*} [Finite C] (invariant : (Fin n → M) → C)
    (complete : ∀ xs ys, invariant xs = invariant ys →
      ∃ e : M ≃[folkmanLanguage] M, ∀ i, e (xs i) = ys i) :
    ∃ reps : Finset (TaggedTuple M hD n),
      ∀ s, ∃ t ∈ reps, TaggedOrbit M hD s t := by
  classical
  let _ := productRing M hD
  let p := pairing M hD
  let _ := folkmanProductStructure p
  let c := encodingEquiv M hD
  let encoded (xs : TaggedTuple M hD n) : Fin n → M :=
    fun i => c.symm (productValue M hD (xs i))
  let code (xs : TaggedTuple M hD n) : (Fin n → Bool) × C :=
    (fun i => sortTag M hD (xs i), invariant (encoded xs))
  refine exists_finite_representatives_of_invariant code (TaggedOrbit M hD) ?_
  intro xs ys h
  have htag (i : Fin n) : sortTag M hD (xs i) = sortTag M hD (ys i) :=
    congrFun (congrArg Prod.fst h) i
  obtain ⟨e, he⟩ := complete (encoded xs) (encoded ys) (congrArg Prod.snd h)
  let g := (c.comp e).comp c.symm
  let l := folkmanProductEmbeddingLeft p p g.toEmbedding
  let r := folkmanProductEmbeddingRight p p g.toEmbedding
  have hsplit (z) : g z = (l z.1, r z.2) :=
    folkmanProductEmbedding_split p p g.toEmbedding z
  have hl : Function.Surjective l := by
    intro x
    obtain ⟨z, hz⟩ := g.surjective (x, 0)
    exact ⟨z.1, congrArg Prod.fst ((hsplit z).symm.trans hz)⟩
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨z, hz⟩ := g.surjective (0, y)
    exact ⟨z.2, congrArg Prod.snd ((hsplit z).symm.trans hz)⟩
  let el := RingEquiv.ofBijective l ⟨folkmanProductEmbeddingLeft_injective p p g.toEmbedding, hl⟩
  let er := RingEquiv.ofBijective r ⟨folkmanProductEmbeddingRight_injective p p g.toEmbedding, hr⟩
  change ∃ (el : leftSort M hD ≃+* leftSort M hD)
    (er : rightSort M hD ≃+* rightSort M hD),
    (∀ x y, p (el x) (er y) = p x y) ∧ ∀ i, Sum.map el er (xs i) = ys i
  refine ⟨el, er, folkmanProductEmbedding_preserves_pairing p p g.toEmbedding, ?_⟩
  intro i
  have hcoord : (l (productValue M hD (xs i)).1, r (productValue M hD (xs i)).2) =
      productValue M hD (ys i) := by
    rw [← hsplit]
    change c (e (c.symm (productValue M hD (xs i)))) = _
    rw [he i, c.apply_symm_apply]
  have hi := htag i
  cases hx : xs i with
  | inl x =>
    cases hy : ys i with
    | inl y =>
      change Sum.inl (l x) = Sum.inl y
      apply congrArg Sum.inl
      simpa [hx, hy, productValue] using congrArg Prod.fst hcoord
    | inr y => simp [sortTag, hx, hy] at hi
  | inr x =>
    cases hy : ys i with
    | inl y => simp [sortTag, hx, hy] at hi
    | inr y =>
      change Sum.inr (r x) = Sum.inr y
      apply congrArg Sum.inr
      simpa [hx, hy, productValue] using congrArg Prod.snd hcoord

end SuccessorTree.NonPrecompact.FolkmanDecoding
