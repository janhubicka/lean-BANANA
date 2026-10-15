import BANANA.NonPrecompact.PrebananaFiveAryWordStage

/-!
# Parity of descendants of an arbitrary five-ary atom

Rather than assuming the root has mark zero, start from an arbitrary
p : F₂ and extend by five children with marks 0, 0, 1, 1, p.
For every refinement depth, the total F₂ mark of all descendants
is the original parent mark. This is the per-fibre parity invariant
needed by the proposed finite-extension construction.

This does not yet count the marked and unmarked descendants,
identify a suffix with descendants in the full tower, or prove the
finite-extension property.
-/

namespace SuccessorTree.NonPrecompact

/-- The mark of a length-k refinement word below a parent of mark p. -/
def prebananaFiveAryDescendantMark (p : F2) :
    (k : ℕ) → PrebananaFiveAryWord k → F2
  | 0, _ => p
  | k + 1, w =>
      prebananaFiveAryChildMark
        (prebananaFiveAryDescendantMark p k (Fin.init w))
        (w (Fin.last k))

/-- Extending a suffix by one letter applies the child-marking rule. -/
theorem prebananaFiveAryDescendantMark_snoc
    (p : F2) (k : ℕ) (w : PrebananaFiveAryWord k) (c : Fin 5) :
    prebananaFiveAryDescendantMark p (k + 1) (Fin.snoc w c) =
      prebananaFiveAryChildMark
        (prebananaFiveAryDescendantMark p k w) c := by
  simp [prebananaFiveAryDescendantMark]

/-- All immediate descendants of an arbitrary marked suffix
have the same total parity as their common parent. -/
theorem prebananaFiveAryDescendantMark_sum_children
    (p : F2) (k : ℕ) (w : PrebananaFiveAryWord k) :
    (∑ c : Fin 5,
      prebananaFiveAryDescendantMark p (k + 1) (Fin.snoc w c)) =
        prebananaFiveAryDescendantMark p k w := by
  simp only [prebananaFiveAryDescendantMark_snoc]
  exact prebananaFiveAryChildMark_total _

/-- At every depth, descendants of a single parent have
total F₂ mark equal to the original parent mark. -/
theorem prebananaFiveAryDescendantMark_total (p : F2) (k : ℕ) :
    (∑ w : PrebananaFiveAryWord k,
      prebananaFiveAryDescendantMark p k w) = p := by
  induction k with
  | zero =>
      simp [prebananaFiveAryDescendantMark]
  | succ k ih =>
      classical
      let e : (Fin 5 × PrebananaFiveAryWord k) ≃
          PrebananaFiveAryWord (k + 1) :=
        Fin.snocEquiv (fun _ : Fin (k + 1) => Fin 5)
      have hs :
          (∑ w : PrebananaFiveAryWord (k + 1),
            prebananaFiveAryDescendantMark p (k + 1) w) =
          ∑ q : Fin 5 × PrebananaFiveAryWord k,
            prebananaFiveAryDescendantMark p (k + 1)
              (Fin.snoc q.2 q.1) := by
        exact (Fintype.sum_equiv e
          (fun q => prebananaFiveAryDescendantMark p (k + 1)
            (Fin.snoc q.2 q.1))
          (prebananaFiveAryDescendantMark p (k + 1))
          (fun q => rfl)).symm
      calc
        (∑ w : PrebananaFiveAryWord (k + 1),
          prebananaFiveAryDescendantMark p (k + 1) w) =
            ∑ q : Fin 5 × PrebananaFiveAryWord k,
              prebananaFiveAryDescendantMark p (k + 1)
                (Fin.snoc q.2 q.1) := hs
        _ = ∑ c : Fin 5, ∑ w : PrebananaFiveAryWord k,
              prebananaFiveAryDescendantMark p (k + 1) (Fin.snoc w c) := by
              rw [Fintype.sum_prod_type]
        _ = ∑ w : PrebananaFiveAryWord k, ∑ c : Fin 5,
              prebananaFiveAryDescendantMark p (k + 1) (Fin.snoc w c) := by
              rw [Finset.sum_comm]
        _ = ∑ w : PrebananaFiveAryWord k,
              prebananaFiveAryDescendantMark p k w := by
              simp only [prebananaFiveAryDescendantMark_sum_children]
        _ = p := ih

end SuccessorTree.NonPrecompact
