import BANANA.NonPrecompact.PrebananaFiveAryCylinderFiniteTuplePresentation
import BANANA.NonPrecompact.PrebananaAbstractMarkedTupleProfile
import BANANA.NonPrecompact.PrebananaFiniteOrbitCriterion

/-!
# Finite marked tuple profiles on the countable pre-BANANA algebra

Every finite tuple in the countable five-ary cylinder algebra
has a finite marked Boolean presentation. We choose such a
presentation (noncomputably) and use the already verified
finite membership-pattern/marking profile on that finite model.

The profile has a finite codomain independent of the number of
atoms in the selected finite presentation. Thus the quotient by
equality of these chosen profiles is finite.

**Important:** The canonical automorphism-orbit relation is
not used here. Identifying equality of finite profiles with a
global automorphism requires the separate ultrahomogeneity and
generated-subalgebra transfer proofs. No claim of finite
automorphism orbit degrees or ω-categoricity is made yet.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- A genuine finite marked Boolean presentation of a specified
tuple of the countable cylinder algebra. -/
structure PrebananaCylinderTupleWitness
    {n : ℕ}
    (xs : Fin n → PrebananaFiveAryCylinderLimitCarrier) where
  model : PrebananaFiniteBooleanModel
  embedding : PrebananaFiniteToCountableEmbedding
    model prebananaCylinderCountableModel
  tuple : Fin n → model.carrier
  covers : ∀ i : Fin n, embedding.hom (tuple i) = xs i

/-- Choose one marked finite presentation of a tuple.
Its existence is kernel-verified independently. -/
noncomputable def prebananaCylinderTupleWitness
    {n : ℕ} (xs : Fin n → PrebananaFiveAryCylinderLimitCarrier) :
    PrebananaCylinderTupleWitness xs :=
  Classical.choice (by
    obtain ⟨A, e, ys, hys⟩ :=
      prebananaCylinder_exists_finiteTuplePresentation xs
    exact ⟨⟨A, e, ys, hys⟩⟩)

/-- The complete finite membership-pattern and F₂-mark profile
of a countable cylinder tuple, measured in one finite marked
presentation. The codomain is finite for each tuple length. -/
noncomputable def prebananaCylinderTupleProfile
    {n : ℕ} (xs : Fin n → PrebananaFiveAryCylinderLimitCarrier) :
    Finset (Fin n → Bool) × ((Fin n → Bool) → F2) :=
  let w := prebananaCylinderTupleWitness xs
  prebananaAbstractMarkedTupleProfile
    w.model.carrier w.model.μ
    w.model.μ_bot w.model.μ_top w.model.μ_add w.tuple

/-- Equivalence under equality of the selected finite profiles.
This is not yet the orbit relation of the automorphism group. -/
noncomputable def prebananaCylinderTupleProfileSetoid (n : ℕ) :
    Setoid (Fin n → PrebananaFiveAryCylinderLimitCarrier) where
  r xs ys :=
    prebananaCylinderTupleProfile xs =
      prebananaCylinderTupleProfile ys
  iseqv := by
    constructor
    · intro xs
      rfl
    · intro xs ys h
      exact h.symm
    · intro xs ys zs hxy hyz
      exact hxy.trans hyz

/-- The quotient of countable cylinder n-tuples by equal finite
profiles has finitely many classes, even before proving that
profiles classify actual automorphism orbits. -/
theorem prebananaCylinderTupleProfile_quotient_finite (n : ℕ) :
    Finite (Quotient (prebananaCylinderTupleProfileSetoid n)) := by
  letI : Setoid (Fin n → PrebananaFiveAryCylinderLimitCarrier) :=
    prebananaCylinderTupleProfileSetoid n
  exact prebananaFiniteProfile_quotient_finite n
    prebananaCylinderTupleProfile
    (by intro xs ys h; exact h)

/-- The chosen finite tuple presentation transports the F₂
mark of every individual coordinate exactly. -/
theorem prebananaCylinderTupleWitness_preserves_coordinate_mark
    {n : ℕ} (xs : Fin n → PrebananaFiveAryCylinderLimitCarrier)
    (i : Fin n) :
    prebananaFiveAryCylinderMark (xs i) =
      (prebananaCylinderTupleWitness xs).model.μ
        ((prebananaCylinderTupleWitness xs).tuple i) := by
  let w := prebananaCylinderTupleWitness xs
  have h := w.embedding.preserves_μ (w.tuple i)
  rw [w.covers i] at h
  exact h

end SuccessorTree.NonPrecompact
