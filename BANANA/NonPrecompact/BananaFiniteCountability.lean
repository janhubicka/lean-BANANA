import BANANA.NonPrecompact.BananaFiniteFraisseProperties
import Mathlib.Data.Fintype.OfMap

/-!
# Countability and unbounded dimensions for finite BANANA pairings

Every finite BANANA pairing has a standard-coordinate presentation:
a pair of dimensions and a finite rectangular matrix over F₂.
For fixed dimensions there are finitely many such matrices. Thus
the collection of all finite standard-coordinate presentations is
countable. Perfect pairings in arbitrarily large dimensions supply
structures of unbounded finite size.

The argument concerns the finite class and does not construct the
countable Fraïssé limit or establish its ω-categoricity.
-/

namespace SuccessorTree.NonPrecompact

/-- For fixed left/right dimensions there are finitely many possible
BANANA pairing matrices. -/
noncomputable instance bananaMatrixStructureFintype (l r : ℕ) :
    Fintype (BananaMatrixStructure l r) := by
  classical
  let toMatrix : BananaMatrixStructure l r → Matrix (Fin l) (Fin r) F2 :=
    fun A => A.pairing
  have hinj : Function.Injective toMatrix := by
    intro A B h
    cases A with
    | mk MA =>
      cases B with
      | mk MB =>
        cases h
        rfl
  exact Fintype.ofInjective toMatrix hinj

/-- A convenient countable type of standard-coordinate presentations
of all finite BANANA structures. -/
abbrev FiniteBananaPresentation :=
  Σ l : ℕ, Σ r : ℕ, BananaMatrixStructure l r

/-- There are only countably many finite BANANA presentations
(and therefore at most countably many isomorphism types). -/
noncomputable instance finiteBananaPresentationCountable :
    Countable FiniteBananaPresentation := by
  classical
  infer_instance

/-- There are finite BANANA structures with arbitrarily large
dimensions in *both* sorts. In particular their carriers have
unbounded finite cardinalities. -/
theorem BananaMatrixStructure.exists_arbitrarily_large_dimensions
    (n : ℕ) :
    ∃ l r : ℕ, ∃ A : BananaMatrixStructure l r,
      n ≤ l ∧ n ≤ r := by
  exact ⟨n, n, perfectBanana n, le_refl _, le_refl _⟩

end SuccessorTree.NonPrecompact
