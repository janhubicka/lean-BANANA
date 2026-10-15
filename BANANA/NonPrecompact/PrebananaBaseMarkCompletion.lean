import BANANA.NonPrecompact.PrebananaFibrewiseSum

/-!
# Marking the distinguished bin in each finite base fibre

For any finite atom allocation f commuting with source and target base
projections, suppose source and target markings have equal sums over
*each* base atom, and every non-distinguished target bin already has
the prescribed mark.

The remaining distinguished bin in each base fibre must also have
its prescribed marking: regroup the source sum by f, remove the
distinguished target atom from the finite sum, and cancel the known
contributions. This lemma uses the per-base rather than merely global
marking hypothesis. It is independent of how witness atoms are chosen.

The full finite-extension theorem still requires the existence of a
compatible witness injection and its composition with the tower.
-/

namespace SuccessorTree.NonPrecompact

/-- Correct markings in all non-distinguished target bins plus
per-base total compatibility imply correct markings in every bin. -/
theorem prebananaBaseMarkCompletion
    {α β δ : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] [DecidableEq δ]
    (source : α → δ) (target : β → δ) (f : α → β)
    (hcomm : ∀ x, target (f x) = source x)
    (markA : α → F2) (markB : β → F2)
    (base : δ → β) (hbase : ∀ a, target (base a) = a)
    (hlocal : ∀ a : δ,
      (∑ x : α, if source x = a then markA x else 0) =
        ∑ b : β, if target b = a then markB b else 0)
    (hother : ∀ b : β, b ≠ base (target b) →
      (∑ x : α, if f x = b then markA x else 0) = markB b)
    (b : β) :
    (∑ x : α, if f x = b then markA x else 0) = markB b := by
  classical
  let F : β → F2 := fun c =>
    ∑ x : α, if f x = c then markA x else 0
  change F b = markB b
  let a : δ := target b
  by_cases hb : b = base a
  · let S : Finset β := Finset.univ.filter (fun c => target c = a)
    have hmem : base a ∈ S := by
      simp [S, hbase a]
    have hflatten :
        (∑ c ∈ S, F c) =
        ∑ c : β, ∑ x : α,
          if target c = a ∧ f x = c then markA x else 0 := by
      calc
        (∑ c ∈ S, F c) =
          ∑ c : β, if target c = a then F c else 0 := by
            simp [S, Finset.sum_filter]
        _ = ∑ c : β, ∑ x : α,
            if target c = a ∧ f x = c then markA x else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          by_cases ht : target c = a
          · simp [ht, F]
          · simp [ht, F]
    have hsum :
        (∑ c ∈ S, F c) = ∑ c ∈ S, markB c := by
      calc
        (∑ c ∈ S, F c) =
          ∑ c : β, ∑ x : α,
            if target c = a ∧ f x = c then markA x else 0 :=
              hflatten
        _ = ∑ x : α, if source x = a then markA x else 0 :=
              prebananaFibrewiseSum_identity source target f hcomm markA a
        _ = ∑ c : β, if target c = a then markB c else 0 :=
              hlocal a
        _ = ∑ c ∈ S, markB c := by
              simp [S, Finset.sum_filter]
    have hrest :
        (∑ c ∈ S.erase (base a), F c) =
          ∑ c ∈ S.erase (base a), markB c := by
      apply Finset.sum_congr rfl
      intro c hc
      have hca : target c = a := by
        have hm : c ∈ S := Finset.mem_of_mem_erase hc
        simpa [S] using hm
      have hne : c ≠ base a := Finset.ne_of_mem_erase hc
      have hne' : c ≠ base (target c) := by simpa [hca] using hne
      simpa [F] using hother c hne'
    have hsplit :
        (∑ c ∈ S.erase (base a), F c) + F (base a) =
          (∑ c ∈ S.erase (base a), markB c) + markB (base a) := by
      calc
        (∑ c ∈ S.erase (base a), F c) + F (base a) =
            ∑ c ∈ S, F c :=
              Finset.sum_erase_add S F hmem
        _ = ∑ c ∈ S, markB c := hsum
        _ = (∑ c ∈ S.erase (base a), markB c) + markB (base a) :=
              (Finset.sum_erase_add S markB hmem).symm
    rw [hrest] at hsplit
    rw [hb]
    exact add_left_cancel hsplit
  · exact hother b (by simpa [a] using hb)

end SuccessorTree.NonPrecompact
