import BANANA.NonPrecompact.PrebananaFiveAryBooleanStage

/-!
# The finite Boolean embedding induced by five-ary prefix maps

A Boolean subset of words of length n lifts to the set of all its
five-ary one-letter extensions at length n+1.

This file proves preservation of the bounded-lattice operations
and injectivity. Preservation of the F₂ marking is a separate
obligation, to be discharged using the child-mark fibre sums.
-/

namespace SuccessorTree.NonPrecompact

/-- Inverse image of a finite subset under the word-prefix projection. -/
def prebananaFiveAryWordLift (n : ℕ)
    (s : Finset (PrebananaFiveAryWord n)) :
    Finset (PrebananaFiveAryWord (n + 1)) :=
  Finset.univ.filter fun w => prebananaFiveAryPrefix n w ∈ s

/-- The one-step word lift is a bounded-lattice homomorphism. -/
def prebananaFiveAryWordLiftHom (n : ℕ) :
    BoundedLatticeHom
      (Finset (PrebananaFiveAryWord n))
      (Finset (PrebananaFiveAryWord (n + 1))) where
  toFun := prebananaFiveAryWordLift n
  map_bot' := by
    ext w
    simp [prebananaFiveAryWordLift]
  map_top' := by
    ext w
    simp [prebananaFiveAryWordLift]
  map_sup' := by
    intro s t
    ext w
    simp [prebananaFiveAryWordLift]
  map_inf' := by
    intro s t
    ext w
    simp [prebananaFiveAryWordLift]

/-- The inverse-image map is injective, since each word has at least
one extension and the prefix projection is surjective. -/
theorem prebananaFiveAryWordLift_injective (n : ℕ) :
    Function.Injective (prebananaFiveAryWordLift n) := by
  intro s t h
  ext w
  obtain ⟨v, hv⟩ := prebananaFiveAryPrefix_surjective n w
  have hmem := congrArg
    (fun u : Finset (PrebananaFiveAryWord (n + 1)) => v ∈ u) h
  simpa [prebananaFiveAryWordLift, hv] using hmem

/-- The bounded-lattice map is also injective. -/
theorem prebananaFiveAryWordLiftHom_injective (n : ℕ) :
    Function.Injective (prebananaFiveAryWordLiftHom n) :=
  prebananaFiveAryWordLift_injective n

end SuccessorTree.NonPrecompact
