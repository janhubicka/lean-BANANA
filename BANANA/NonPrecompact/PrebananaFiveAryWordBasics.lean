import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.NormNum

/-!
# Finite five-ary words and marks

Each atom has five children, of which two have mark zero and two
have mark one. The last child keeps the parent's mark. The definitions
and parity lemmas need only the finite word types and the binary field.
-/

namespace SuccessorTree.NonPrecompact

/-- A five-child marking with two fixed zero marks, two fixed one
marks, and a fifth mark inherited from the parent. -/
def prebananaFiveAryChildMark (p : ZMod 2) (i : Fin 5) : ZMod 2 :=
  if i = 4 then p else if i = 2 ∨ i = 3 then 1 else 0

/-- There are always two explicitly unmarked children. -/
theorem prebananaFiveAryChildMark_zeros (p : ZMod 2) :
    prebananaFiveAryChildMark p 0 = 0 ∧
      prebananaFiveAryChildMark p 1 = 0 := by
  simp [prebananaFiveAryChildMark]

/-- There are always two explicitly marked children. -/
theorem prebananaFiveAryChildMark_ones (p : ZMod 2) :
    prebananaFiveAryChildMark p 2 = 1 ∧
      prebananaFiveAryChildMark p 3 = 1 := by
  simp [prebananaFiveAryChildMark]

/-- The last child inherits the parent's marking. -/
theorem prebananaFiveAryChildMark_last (p : ZMod 2) :
    prebananaFiveAryChildMark p 4 = p := by
  rfl

/-- The sum of all five children's marks equals the parent's
mark. This is the finite compatibility needed by the tower
embeddings on the Boolean algebra of sets of words. -/
theorem prebananaFiveAryChildMark_total (p : ZMod 2) :
    (∑ i : Fin 5, prebananaFiveAryChildMark p i) = p := by
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  norm_num [Fin.sum_univ_succ, prebananaFiveAryChildMark]
  simpa only [← add_assoc, htwo, zero_add]

/-- A word of length n over a five-letter alphabet. -/
abbrev PrebananaFiveAryWord (n : ℕ) := Fin n → Fin 5

/-- Recursively mark the finite words of a five-ary tree.
The empty word has mark zero. -/
def prebananaFiveAryWordMark :
    (n : ℕ) → PrebananaFiveAryWord n → ZMod 2
  | 0, _ => 0
  | n + 1, w =>
      prebananaFiveAryChildMark
        (prebananaFiveAryWordMark n (fun i => w i.castSucc))
        (w (Fin.last n))

/-- Extending a word by one letter applies exactly the
five-ary child-mark rule to its previous mark. -/
theorem prebananaFiveAryWordMark_snoc
    (n : ℕ) (w : PrebananaFiveAryWord n) (c : Fin 5) :
    prebananaFiveAryWordMark (n + 1) (Fin.snoc w c) =
      prebananaFiveAryChildMark (prebananaFiveAryWordMark n w) c := by
  simp [prebananaFiveAryWordMark]

/-- The marks of all five immediate children sum to the
mark of their common parent. -/
theorem prebananaFiveAryWordMark_sum_children
    (n : ℕ) (w : PrebananaFiveAryWord n) :
    (∑ c : Fin 5, prebananaFiveAryWordMark (n + 1)
        (Fin.snoc w c)) = prebananaFiveAryWordMark n w := by
  simp only [prebananaFiveAryWordMark_snoc]
  exact prebananaFiveAryChildMark_total _

/-- The empty word has mark zero. -/
theorem prebananaFiveAryWordMark_empty
    (w : PrebananaFiveAryWord 0) :
    prebananaFiveAryWordMark 0 w = 0 := rfl

/-- At every length the total parity of all word atoms is zero. -/
theorem prebananaFiveAryWordMark_total (n : ℕ) :
    (∑ w : PrebananaFiveAryWord n, prebananaFiveAryWordMark n w) = 0 := by
  induction n with
  | zero =>
      simp [prebananaFiveAryWordMark]
  | succ n ih =>
      classical
      let e : (Fin 5 × PrebananaFiveAryWord n) ≃
          PrebananaFiveAryWord (n + 1) :=
        Fin.snocEquiv (fun _ : Fin (n + 1) => Fin 5)
      have hs :
          (∑ w : PrebananaFiveAryWord (n + 1),
            prebananaFiveAryWordMark (n + 1) w) =
          ∑ p : Fin 5 × PrebananaFiveAryWord n,
            prebananaFiveAryWordMark (n + 1) (Fin.snoc p.2 p.1) := by
        exact (Fintype.sum_equiv e
          (fun p => prebananaFiveAryWordMark (n + 1)
            (Fin.snoc p.2 p.1))
          (prebananaFiveAryWordMark (n + 1))
          (fun p => rfl)).symm
      calc
        (∑ w : PrebananaFiveAryWord (n + 1),
          prebananaFiveAryWordMark (n + 1) w) =
            ∑ p : Fin 5 × PrebananaFiveAryWord n,
              prebananaFiveAryWordMark (n + 1)
                (Fin.snoc p.2 p.1) := hs
        _ = ∑ c : Fin 5, ∑ w : PrebananaFiveAryWord n,
              prebananaFiveAryWordMark (n + 1) (Fin.snoc w c) := by
              rw [Fintype.sum_prod_type]
        _ = ∑ w : PrebananaFiveAryWord n, ∑ c : Fin 5,
              prebananaFiveAryWordMark (n + 1) (Fin.snoc w c) := by
              rw [Finset.sum_comm]
        _ = ∑ w : PrebananaFiveAryWord n,
              prebananaFiveAryWordMark n w := by
              simp only [prebananaFiveAryWordMark_sum_children]
        _ = 0 := ih

/-- Delete the last letter of a five-ary word. -/
def prebananaFiveAryPrefix (n : ℕ) :
    PrebananaFiveAryWord (n + 1) → PrebananaFiveAryWord n :=
  Fin.init

/-- Appending any child letter and then dropping it recovers the parent. -/
theorem prebananaFiveAryPrefix_snoc (n : ℕ)
    (w : PrebananaFiveAryWord n) (c : Fin 5) :
    prebananaFiveAryPrefix n (Fin.snoc w c) = w := by
  simpa [prebananaFiveAryPrefix] using (Fin.init_snoc c w)

/-- Every finite word admits a one-step extension. -/
theorem prebananaFiveAryPrefix_surjective (n : ℕ) :
    Function.Surjective (prebananaFiveAryPrefix n) := by
  intro w
  exact ⟨Fin.snoc w 0, prebananaFiveAryPrefix_snoc n w 0⟩

/-- Any extended word is determined by its prefix and its final letter. -/
theorem prebananaFiveAryPrefix_snoc_last (n : ℕ)
    (w : PrebananaFiveAryWord (n + 1)) :
    Fin.snoc (prebananaFiveAryPrefix n w) (w (Fin.last n)) = w := by
  exact Fin.snoc_init_self w

/-- The five extensions of a prefix carry exactly the total
mark prescribed for the prefix. -/
theorem prebananaFiveAryPrefix_mark_sum (n : ℕ)
    (w : PrebananaFiveAryWord n) :
    (∑ c : Fin 5,
        prebananaFiveAryWordMark (n + 1) (Fin.snoc w c)) =
      prebananaFiveAryWordMark n w :=
  prebananaFiveAryWordMark_sum_children n w

end SuccessorTree.NonPrecompact
