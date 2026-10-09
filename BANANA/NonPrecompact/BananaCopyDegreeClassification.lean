import BANANA.NonPrecompact.BananaCopyDegree
import BANANA.NonPrecompact.BananaOneSidedCopyDegree

/-!
# Standard-coordinate BANANA copy-degree classification

This file assembles the two *unlabelled copy* cases into the statement
of the circulation classification theorem for finite matrix presentations:
a zero sort gives copy degree exactly one, while two positive sorts give
unbounded copy Ramsey degrees.

The upstream successor-tree GLR representation and the direct two-sided
copy-degree formalisation are currently uncompiled source. Consequently
this wrapper is also only a staged proof attempt, not a Lean certificate.
-/

namespace SuccessorTree.NonPrecompact

/-- Standard-coordinate form of the manuscript's complete copy
Ramsey-degree classification. The positive sort cases need no
non-degeneracy assumption on the bilinear pairing. -/
theorem BananaMatrixStructure.copyDegreeClassification
    {l r : ℕ} (A : BananaMatrixStructure l r) :
    (l = 0 → A.copyRamseyDegreeLE 1 ∧ ¬ A.copyRamseyDegreeLE 0) ∧
    (r = 0 → A.copyRamseyDegreeLE 1 ∧ ¬ A.copyRamseyDegreeLE 0) ∧
    (0 < l → 0 < r → ∀ t : ℕ, ¬ A.copyRamseyDegreeLE t) := by
  constructor
  · intro hl
    subst l
    exact A.rightOnly_copy_degree_exactly_one
  constructor
  · intro hr
    subst r
    exact A.leftOnly_copy_degree_exactly_one
  · intro hl hr
    exact A.copyRamseyDegree_infinite_of_positive hl hr

end SuccessorTree.NonPrecompact
