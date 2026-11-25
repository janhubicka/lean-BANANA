import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

/-!
# Presenting a finite closure family by unary operations and one binary operation

For an intersection-closed cofinal family of finite sets, distinguish a generator of
each member under a fixed collection of unary operations. One additional binary
operation suffices to make precisely those finite sets closed, among the sets
containing the least member.
-/

namespace SuccessorTree.NonPrecompact

universe u v

variable {M : Type u} [DecidableEq M]

/-- A cofinal, intersection-closed collection of finite subsets of a fixed carrier. -/
structure FiniteSetClosureFamily (M : Type u) [DecidableEq M] where
  members : Set (Finset M)
  cofinal (s : Finset M) : ∃ t ∈ members, s ⊆ t
  inter_mem {s t : Finset M} : s ∈ members → t ∈ members → s ∩ t ∈ members

namespace FiniteSetClosureFamily

variable (F : FiniteSetClosureFamily M)

theorem exists_least_member (s : Finset M) :
    ∃ t ∈ F.members, s ⊆ t ∧ ∀ r ∈ F.members, s ⊆ r → t ⊆ r := by
  classical
  let HasSize (n : ℕ) := ∃ t ∈ F.members, s ⊆ t ∧ t.card = n
  have hSize : ∃ n, HasSize n := by
    obtain ⟨t, ht, hst⟩ := F.cofinal s
    exact ⟨t.card, t, ht, hst, rfl⟩
  obtain ⟨t, ht, hst, hcard⟩ := Nat.find_spec hSize
  refine ⟨t, ht, hst, fun r hr hsr => ?_⟩
  have hsub : s ⊆ t ∩ r := Finset.subset_inter hst hsr
  have hle : t.card ≤ (t ∩ r).card := by
    rw [hcard]
    exact Nat.find_min' hSize ⟨t ∩ r, F.inter_mem ht hr, hsub, rfl⟩
  have heq := Finset.eq_of_subset_of_card_le (Finset.inter_subset_left (s₁ := t) (s₂ := r)) hle
  simpa only [heq] using (Finset.inter_subset_right (s₁ := t) (s₂ := r))

/-- The least selected set containing the given finite set. -/
noncomputable def envelope (s : Finset M) : Finset M :=
  (F.exists_least_member s).choose

theorem envelope_mem (s : Finset M) : F.envelope s ∈ F.members :=
  (F.exists_least_member s).choose_spec.1

theorem subset_envelope (s : Finset M) : s ⊆ F.envelope s :=
  (F.exists_least_member s).choose_spec.2.1

theorem envelope_subset {s t : Finset M} (ht : t ∈ F.members) (hst : s ⊆ t) :
    F.envelope s ⊆ t :=
  (F.exists_least_member s).choose_spec.2.2 t ht hst

/-- Closure under a specified family of unary operations. -/
def UnaryClosed {ι : Type v} (unary : ι → M → M) (s : Finset M) : Prop :=
  ∀ i x, x ∈ s → unary i x ∈ s

/-- Every selected member has a distinguished point generating it under the same
unary operations. The family of operations may in particular be finite. -/
structure UnaryGenerators (ι : Type v) where
  operation : ι → M → M
  closed {s : Finset M} : s ∈ F.members → UnaryClosed operation s
  generator : {s : Finset M // s ∈ F.members} → M
  generator_mem (s : {s : Finset M // s ∈ F.members}) : generator s ∈ s.val
  subset_of_generator_mem (s : {s : Finset M // s ∈ F.members}) {t : Finset M} :
    UnaryClosed operation t → generator s ∈ t → s.val ⊆ t

namespace UnaryGenerators

variable {F} {ι : Type v} (G : F.UnaryGenerators ι)

/-- Return a generator of the least selected set containing both inputs. -/
noncomputable def join (x y : M) : M :=
  G.generator ⟨F.envelope {x, y}, F.envelope_mem {x, y}⟩

theorem join_mem {s : Finset M} (hs : s ∈ F.members) {x y : M}
    (hx : x ∈ s) (hy : y ∈ s) : G.join x y ∈ s :=
  F.envelope_subset hs (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
    (G.generator_mem _)

/-- Among the finite sets containing the least selected set, joint closure under
the unary operations and one binary operation is exactly membership in the family. -/
theorem mem_iff_closed (s : Finset M) :
    s ∈ F.members ↔
      F.envelope ∅ ⊆ s ∧ UnaryClosed G.operation s ∧
      ∀ x ∈ s, ∀ y ∈ s, G.join x y ∈ s := by
  refine ⟨fun hs => ⟨F.envelope_subset hs (Finset.empty_subset s), G.closed hs,
    fun _ hx _ hy => G.join_mem hs hx hy⟩, ?_⟩
  rintro ⟨hbase, hunary, hjoin⟩
  have hEnvelope (t : Finset M) (hst : t ⊆ s) : F.envelope t ⊆ s := by
    induction t using Finset.induction_on with
    | empty => exact hbase
    | @insert x t hxt ih =>
        have hx : x ∈ s := hst (Finset.mem_insert_self _ _)
        have ht : F.envelope t ⊆ s := ih (Finset.subset_insert _ _ |>.trans hst)
        let y := G.generator ⟨F.envelope t, F.envelope_mem t⟩
        have hy : y ∈ s := ht (G.generator_mem _)
        have hj := hjoin x hx y hy
        have hxy := F.subset_envelope {x, y}
        have hty : F.envelope t ⊆ F.envelope {x, y} :=
          G.subset_of_generator_mem ⟨F.envelope t, F.envelope_mem t⟩
            (G.closed (F.envelope_mem _))
            (hxy (Finset.mem_insert_of_mem (Finset.mem_singleton_self y)))
        have hins : insert x t ⊆ F.envelope {x, y} := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hxy (Finset.mem_insert_self _ _)
          · exact hty (F.subset_envelope t hz)
        exact (F.envelope_subset (F.envelope_mem _) hins).trans
          (G.subset_of_generator_mem ⟨F.envelope {x, y}, F.envelope_mem _⟩ hunary hj)
  have heq : F.envelope s = s :=
    Finset.Subset.antisymm (hEnvelope s fun _ h => h) (F.subset_envelope s)
  rw [← heq]
  exact F.envelope_mem s

end UnaryGenerators
end FiniteSetClosureFamily
end SuccessorTree.NonPrecompact
