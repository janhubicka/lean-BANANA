import BANANA.NonPrecompact.PrebananaFiveAryWordLevelAllocation
import BANANA.NonPrecompact.PrebananaFiveAryBooleanStage

/-!
# Marked powerset embeddings induced by finite atom allocations

A surjective map from finite ambient atoms to finite target atoms
induces an injective inverse-image Boolean-algebra homomorphism.
Preservation of the F₂ marking on every atom fibre implies
preservation on every Boolean element.

The finite sum identity is stated over an arbitrary commutative
additive monoid, so the same combinatorial proof can be reused for
Folkman integer incidence counts. This module packages the
pre-BANANA specialisation into genuine marked Boolean embeddings.
-/

namespace SuccessorTree.NonPrecompact

/-- Sum over the preimage of a finite set of labels, regrouped into
the disjoint fibres of a total atom-owner map. -/
theorem finiteOwner_sum_subset
    {α β R : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [AddCommMonoid R]
    (owner : α → β) (weight : α → R) (s : Finset β) :
    (∑ x ∈ (Finset.univ.filter (fun x : α => owner x ∈ s)),
      weight x) =
      ∑ b ∈ s, ∑ x ∈ (Finset.univ.filter
        (fun x : α => owner x = b)), weight x := by
  classical
  let fibre : β → Finset α :=
    fun b => Finset.univ.filter (fun x : α => owner x = b)
  have hd : (s : Set β).PairwiseDisjoint fibre := by
    intro b hb c hc hne
    change Disjoint (fibre b) (fibre c)
    rw [Finset.disjoint_left]
    intro x hbx hcx
    have h₁ : owner x = b := (Finset.mem_filter.mp hbx).2
    have h₂ : owner x = c := (Finset.mem_filter.mp hcx).2
    exact hne (h₁.symm.trans h₂)
  have hcover :
      (Finset.univ.filter (fun x : α => owner x ∈ s)) =
        s.biUnion fibre := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_biUnion, fibre]
    constructor
    · intro hx
      exact ⟨owner x, hx, rfl⟩
    · rintro ⟨b, hb, hx⟩
      simpa [fibre] using (hx.symm ▸ hb)
  calc
    (∑ x ∈ (Finset.univ.filter (fun x : α => owner x ∈ s)),
        weight x) =
      ∑ x ∈ s.biUnion fibre, weight x := by rw [hcover]
    _ = ∑ b ∈ s, ∑ x ∈ fibre b, weight x :=
      Finset.sum_biUnion hd
    _ = ∑ b ∈ s, ∑ x ∈ (Finset.univ.filter
        (fun x : α => owner x = b)), weight x := rfl

/-- A finite, nontrivial powerset Boolean algebra with additive F₂
marking and zero total mark. -/
noncomputable def prebananaFiniteMarkedPowerset
    (β : Type) [Fintype β] [Nonempty β] [DecidableEq β]
    (mark : β → F2)
    (htotal : (∑ b : β, mark b) = 0) :
    PrebananaFiniteBooleanModel where
  carrier := Finset β
  booleanAlgebra := inferInstance
  finite := inferInstance
  nontrivial := by
    classical
    infer_instance
  μ := fun s => ∑ b ∈ s, mark b
  μ_bot := by
    simp
  μ_top := by
    simpa using htotal
  μ_add := by
    intro s t hst
    change (∑ b ∈ s ∪ t, mark b) =
      (∑ b ∈ s, mark b) + (∑ b ∈ t, mark b)
    exact Finset.sum_union
      (Finset.disjoint_iff_inter_eq_empty.mpr hst)

/-- A marked surjective partition of the actual finite five-ary
word atoms induces a genuine marking-preserving Boolean embedding
from the corresponding target powerset into the word stage. -/
noncomputable def prebananaFiveAryOwnerMarkedEmbedding
    (n : ℕ) (β : Type) [Fintype β]
    [DecidableEq β] [Nonempty β]
    (markB : β → F2)
    (htotal : (∑ b : β, markB b) = 0)
    (part : PrebananaFiveAryWord n → β)
    (hsurj : Function.Surjective part)
    (hmark : ∀ b : β,
      (∑ w : PrebananaFiveAryWord n,
        if part w = b then prebananaFiveAryWordMark n w else 0) =
          markB b) :
    PrebananaFiniteBooleanEmbedding
      (prebananaFiniteMarkedPowerset β markB htotal)
      (prebananaFiveAryBooleanStage n) := by
  classical
  refine {
    hom := {
      toFun := fun s => Finset.univ.filter
        (fun w : PrebananaFiveAryWord n => part w ∈ s)
      map_bot' := by
        ext w
        simp
      map_top' := by
        ext w
        simp
      map_sup' := by
        intro s t
        ext w
        simp
      map_inf' := by
        intro s t
        ext w
        simp
    }
    injective := by
      intro s t h
      ext b
      obtain ⟨w, hw⟩ := hsurj b
      have heq := congrArg
        (fun q : Finset (PrebananaFiveAryWord n) => w ∈ q) h
      simpa [hw] using heq
    preserves_μ := by
      intro s
      change
        (∑ w ∈ (Finset.univ.filter
          (fun w : PrebananaFiveAryWord n => part w ∈ s)),
          prebananaFiveAryWordMark n w) =
        ∑ b ∈ s, markB b
      calc
        (∑ w ∈ (Finset.univ.filter
          (fun w : PrebananaFiveAryWord n => part w ∈ s)),
          prebananaFiveAryWordMark n w) =
          ∑ b ∈ s, ∑ w ∈ (Finset.univ.filter
            (fun w : PrebananaFiveAryWord n => part w = b)),
            prebananaFiveAryWordMark n w :=
              finiteOwner_sum_subset part (prebananaFiveAryWordMark n) s
        _ = ∑ b ∈ s, markB b := by
          apply Finset.sum_congr rfl
          intro b hb
          simpa only [Finset.sum_filter] using hmark b
  }

end SuccessorTree.NonPrecompact
