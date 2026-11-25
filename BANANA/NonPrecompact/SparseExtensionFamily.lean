import Mathlib.Basic.Finite.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Sparse families of finite structures

An extension request whose target has (n) points is considered at round (n).
Only sources of size less than (n) can make such a request. Each round also
selects an ambient set to ensure cofinality of the family.
-/

namespace SuccessorTree.NonPrecompact

namespace SparseExtensionFamily

variable {α : Type*} [DecidableEq α] {V : Set (Finset α)}

private structure Stage (V : Set (Finset α)) where
  ambient : Finset α
  known : Finset (Finset α)
  ambient_valid : ambient ∈ V
  known_valid : ∀ A ∈ known, A ∈ V
  within : ∀ A ∈ known, A ⊆ ambient
  intersection : ∀ A ∈ known, ∀ B ∈ known, A ∩ B ∈ known

private structure Growth (n : ℕ) (S T : Stage V) : Prop where
  known_subset : S.known ⊆ T.known
  new_card : ∀ A ∈ T.known, A ∉ S.known → n ≤ A.card

private theorem Growth.refl (n : ℕ) (S : Stage V) : Growth n S S :=
  ⟨fun _ h => h, fun _ h hn => (hn h).elim⟩

private theorem Growth.trans {n : ℕ} {S T U : Stage V}
    (h₁ : Growth n S T) (h₂ : Growth n T U) : Growth n S U where
  known_subset := h₁.known_subset.trans h₂.known_subset
  new_card A hA hn := by
    by_cases ht : A ∈ T.known
    · exact h₁.new_card A ht hn
    · exact h₂.new_card A hA ht

private theorem exists_add_fresh
    (enlarge : ∀ C n, ∃ D ∈ V, C ⊆ D ∧ n ≤ D.card)
    {n : ℕ} (S : Stage V) {A D : Finset α}
    (hA : A ∈ S.known) (hD : D ∈ V) (hinter : D ∩ S.ambient = A)
    (hcard : n ≤ D.card) :
    ∃ T : Stage V, Growth n S T ∧ D ∈ T.known := by
  obtain ⟨ambient, hvalid, hsubset, -⟩ := enlarge (D ∪ S.ambient) 0
  have old_inside : S.ambient ⊆ ambient :=
    Finset.subset_union_right.trans hsubset
  have fresh_inside : D ⊆ ambient :=
    Finset.subset_union_left.trans hsubset
  have fresh_inter {B : Finset α} (hB : B ∈ S.known) : D ∩ B = A ∩ B := by
    rw [← hinter, Finset.inter_assoc, Finset.inter_eq_right.mpr (S.within _ hB)]
  let T : Stage V := {
    ambient := ambient
    known := insert D S.known
    ambient_valid := hvalid
    known_valid := by
      intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact hD
      · exact S.known_valid _ hB
    within := by
      intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact fresh_inside
      · exact (S.within _ hB).trans old_inside
    intersection := by
      intro B hB C hC
      rcases Finset.mem_insert.mp hB with rfl | hB' <;>
        rcases Finset.mem_insert.mp hC with rfl | hC'
      · rw [Finset.inter_self]
        exact Finset.mem_insert_self _ _
      · rw [fresh_inter hC']
        exact Finset.mem_insert_of_mem (S.intersection _ hA _ hC')
      · rw [Finset.inter_comm, fresh_inter hB']
        exact Finset.mem_insert_of_mem (S.intersection _ hA _ hB')
      · exact Finset.mem_insert_of_mem (S.intersection _ hB' _ hC') }
  refine ⟨T, ⟨fun _ h => Finset.mem_insert_of_mem h, ?_⟩, Finset.mem_insert_self _ _⟩
  intro B hB hn
  rcases Finset.mem_insert.mp hB with rfl | hB
  · exact hcard
  · exact (hn hB).elim

private theorem exists_add_ambient
    (enlarge : ∀ C n, ∃ D ∈ V, C ⊆ D ∧ n ≤ D.card)
    (n : ℕ) (S : Stage V) (seed : Finset α) :
    ∃ T : Stage V, Growth n S T ∧ ∃ A ∈ T.known, seed ⊆ A := by
  obtain ⟨D, hD, hsubset, hcard⟩ := enlarge (seed ∪ S.ambient) n
  have old_inside : S.ambient ⊆ D :=
    Finset.subset_union_right.trans hsubset
  let T : Stage V := {
    ambient := D
    known := insert D S.known
    ambient_valid := hD
    known_valid := by
      intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact hD
      · exact S.known_valid _ hB
    within := by
      intro B hB
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact Finset.Subset.rfl
      · exact (S.within _ hB).trans old_inside
    intersection := by
      intro B hB C hC
      rcases Finset.mem_insert.mp hB with rfl | hB' <;>
        rcases Finset.mem_insert.mp hC with rfl | hC'
      · rw [Finset.inter_self]
        exact Finset.mem_insert_self _ _
      · rw [Finset.inter_eq_right.mpr ((S.within _ hC').trans old_inside)]
        exact Finset.mem_insert_of_mem hC'
      · rw [Finset.inter_eq_left.mpr ((S.within _ hB').trans old_inside)]
        exact Finset.mem_insert_of_mem hB'
      · exact Finset.mem_insert_of_mem (S.intersection _ hB' _ hC') }
  refine ⟨T, ⟨fun _ h => Finset.mem_insert_of_mem h, ?_⟩,
    D, Finset.mem_insert_self _ _, Finset.subset_union_left.trans hsubset⟩
  intro B hB hn
  rcases Finset.mem_insert.mp hB with rfl | hB
  · exact hcard
  · exact (hn hB).elim

private theorem exists_answer_requests {ι : Type*} [DecidableEq ι]
    (enlarge : ∀ C n, ∃ D ∈ V, C ⊆ D ∧ n ≤ D.card)
    (n : ℕ) (S : Stage V) (source : ι → Finset α) (goal : ι → Finset α → Prop)
    (source_known : ∀ q, source q ∈ S.known)
    (fresh : ∀ q C, C ∈ V → source q ⊆ C →
      ∃ D ∈ V, D.card = n ∧ D ∩ C = source q ∧ goal q D)
    (requests : Finset ι) :
    ∃ T : Stage V, Growth n S T ∧
      ∀ q ∈ requests, ∃ D ∈ T.known, D.card = n ∧ source q ⊆ D ∧ goal q D := by
  induction requests using Finset.induction_on with
  | empty =>
      exact ⟨S, Growth.refl n S, by simp⟩
  | @insert q requests hq ih =>
      obtain ⟨T, hST, answered⟩ := ih
      have hs := hST.known_subset (source_known q)
      obtain ⟨D, hD, hcard, hinter, hgoal⟩ :=
        fresh q T.ambient T.ambient_valid (T.within _ hs)
      obtain ⟨U, hTU, hnew⟩ :=
        exists_add_fresh enlarge T hs hD hinter hcard.ge
      refine ⟨U, hST.trans hTU, ?_⟩
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact ⟨D, hnew, hcard, hinter ▸ Finset.inter_subset_left, hgoal⟩
      · obtain ⟨E, hE, hsize, hSE, hdone⟩ := answered p hp
        exact ⟨E, hTU.known_subset hE, hsize, hSE, hdone⟩

private theorem exists_round {Q : Finset α → ℕ → Type*}
    (goal : ∀ A n, Q A n → Finset α → Prop)
    (finite_requests : ∀ A n, Finite (Q A n))
    (enlarge : ∀ C n, ∃ D ∈ V, C ⊆ D ∧ n ≤ D.card)
    (fresh : ∀ A C n (q : Q A n), A ∈ V → C ∈ V → A ⊆ C → A.card < n →
      ∃ D ∈ V, D.card = n ∧ D ∩ C = A ∧ goal A n q D)
    (n : ℕ) (S : Stage V) (seed : Finset α) :
    ∃ T : Stage V, Growth n S T ∧
      (∃ A ∈ T.known, seed ⊆ A) ∧
      ∀ A ∈ S.known, A.card < n → ∀ q : Q A n,
        ∃ D ∈ T.known, D.card = n ∧ A ⊆ D ∧ goal A n q D := by
  classical
  let Source := {A : S.known // A.val.card < n}
  let Requests := Σ A : Source, Q A.val.val n
  let (A : Source) : Finite (Q A.val.val n) := finite_requests _ _
  let : Finite Source := by unfold Source; infer_instance
  let : Finite Requests := by unfold Requests; infer_instance
  let : Fintype Requests := Fintype.ofFinite _
  obtain ⟨R, hSR, hanswer⟩ :=
    exists_answer_requests enlarge n S
      (fun q : Requests => q.1.val.val) (fun q D => goal _ n q.2 D)
      (fun q => q.1.val.prop)
      (fun q C hC hsub => fresh _ C n q.2 (S.known_valid _ q.1.val.prop) hC hsub q.1.prop)
      Finset.univ
  obtain ⟨T, hRT, hseed⟩ := exists_add_ambient enlarge n R seed
  refine ⟨T, hSR.trans hRT, hseed, ?_⟩
  intro A hA hsize q
  let request : Requests := ⟨⟨⟨A, hA⟩, hsize⟩, q⟩
  obtain ⟨D, hD, hcard, hsub, hgoal⟩ := hanswer request (Finset.mem_univ request)
  exact ⟨D, hRT.known_subset hD, hcard, hsub, hgoal⟩

private theorem known_of_later {S : ℕ → Stage V}
    (growth : ∀ n, Growth n (S n) (S (n + 1))) {n m : ℕ}
    (hnm : n ≤ m) {A : Finset α} (hA : A ∈ (S m).known) (hsize : A.card < n) :
    A ∈ (S n).known := by
  induction m, hnm using Nat.le_induction with
  | base => exact hA
  | succ m hnm ih =>
      apply ih
      by_contra hn
      exact (Nat.not_le_of_gt (lt_of_lt_of_le hsize hnm)) ((growth m).new_card _ hA hn)

/-- A supply of fresh extensions yields a cofinal, intersection-closed family of
finite carriers. The family retains only finitely many members of each size and
answers every proper extension request issued from one of its own members. -/
theorem exists_sparse_extension_family {Q : Finset α → ℕ → Type*}
    (goal : ∀ A n, Q A n → Finset α → Prop)
    (finite_requests : ∀ A n, Finite (Q A n))
    (enlarge : ∀ C n, ∃ D ∈ V, C ⊆ D ∧ n ≤ D.card)
    (base : Finset α) (base_valid : base ∈ V)
    (seed : ℕ → Finset α) (seed_cofinal : ∀ C, ∃ n, C ⊆ seed n)
    (fresh : ∀ A C n (q : Q A n), A ∈ V → C ∈ V → A ⊆ C → A.card < n →
      ∃ D ∈ V, D.card = n ∧ D ∩ C = A ∧ goal A n q D) :
    ∃ F : Set (Finset α), base ∈ F ∧ F ⊆ V ∧ (∀ C, ∃ D ∈ F, C ⊆ D) ∧
      (∀ A ∈ F, ∀ B ∈ F, A ∩ B ∈ F) ∧
      (∀ n : ℕ, {A ∈ F | A.card = n}.Finite) ∧
      ∀ A ∈ F, ∀ n, A.card < n → ∀ q : Q A n,
        ∃ D ∈ F, D.card = n ∧ A ⊆ D ∧ goal A n q D := by
  classical
  let initial : Stage V := {
    ambient := base
    known := {base}
    ambient_valid := base_valid
    known_valid := by simp [base_valid]
    within := by simp
    intersection := by simp }
  let next (n : ℕ) (T : Stage V) := (exists_round goal finite_requests enlarge fresh n T (seed n)).choose
  let S : ℕ → Stage V := Nat.rec initial next
  have hstep (n : ℕ) := (exists_round goal finite_requests enlarge fresh n (S n) (seed n)).choose_spec
  have growth (n : ℕ) : Growth n (S n) (S (n + 1)) := (hstep n).1
  have mono : Monotone fun n => (S n).known :=
    monotone_nat_of_le_succ fun n => (growth n).known_subset
  let F : Set (Finset α) := {A | ∃ n, A ∈ (S n).known}
  refine ⟨F, ⟨0, Finset.mem_singleton_self base⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rintro A ⟨n, hA⟩
    exact (S n).known_valid _ hA
  · intro C
    obtain ⟨n, hn⟩ := seed_cofinal C
    obtain ⟨D, hD, hseed⟩ := (hstep n).2.1
    exact ⟨D, ⟨n + 1, hD⟩, hn.trans hseed⟩
  · rintro A ⟨n, hA⟩ B ⟨m, hB⟩
    exact ⟨max n m, (S _).intersection A (mono (le_max_left n m) hA)
      B (mono (le_max_right n m) hB)⟩
  · intro n
    apply (S (n + 1)).known.finite_toSet.subset
    rintro A ⟨⟨m, hA⟩, hsize⟩
    rcases le_total m (n + 1) with h | h
    · exact mono h hA
    · exact known_of_later growth h hA (hsize ▸ Nat.lt_succ_self n)
  · rintro A ⟨m, hA⟩ n hsize q
    have hAn : A ∈ (S n).known := by
      rcases le_total m n with h | h
      · exact mono h hA
      · exact known_of_later growth h hA hsize
    obtain ⟨D, hD, hcard, hsub, hgoal⟩ := (hstep n).2.2 A hAn hsize q
    exact ⟨D, ⟨n + 1, hD⟩, hcard, hsub, hgoal⟩

end SparseExtensionFamily

end SuccessorTree.NonPrecompact
