import BANANA.NonPrecompact.BananaAmalgam

/-!
# Strong block amalgamation for finite BANANA pairings

The circulation manuscript proves strong amalgamation after choosing
complements of the two embeddings of the common substructure. Its
pairing matrices then have an identical common block; the other
coordinates are disjoint.

The previous file `BananaAmalgam` proves the raw matrix restriction
and strong intersection lemmas. This file supplies the missing
pairing-preservation statements for the full induced bilinear forms
and packages the resulting split-coordinate strong amalgam.

The claim for *arbitrary* (not already split) diagrams will additionally
need to transport the construction along chosen complements.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- Bilinear evaluation of a rectangular matrix with arbitrary finite
left and right coordinate types. It agrees with the usual
`BananaMatrixStructure.eval` on standard `Fin` coordinates. -/
def indexedBananaPairing
    {L R : Type*} [Fintype L] [Fintype R]
    (M : Matrix L R F2)
    (x : L → F2) (y : R → F2) : F2 :=
  ∑ i : L, ∑ j : R, x i * M i j * y j

/-- On standard finite coordinate sets, the double-sum pairing is
exactly the evaluation function of a BANANA matrix structure. -/
theorem indexedBananaPairing_fin_eq_eval
    {l r : ℕ} (A : BananaMatrixStructure l r)
    (x : Fin l → F2) (y : Fin r → F2) :
    indexedBananaPairing A.pairing x y = A.eval x y := by
  classical
  simp [indexedBananaPairing, BananaMatrixStructure.eval,
    Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- Preservation of both vectors' pairing when taking the first
summand of the block amalgam. -/
theorem indexedBananaPairing_amalgam_left
    {LA RA UB VB UC VC : Type*}
    [Fintype LA] [Fintype RA]
    [Fintype UB] [Fintype VB] [Fintype UC] [Fintype VC]
    (B : Matrix (Sum LA UB) (Sum RA VB) F2)
    (C : Matrix (Sum LA UC) (Sum RA VC) F2)
    (x : Sum LA UB → F2) (y : Sum RA VB → F2) :
    indexedBananaPairing (bananaBlockAmalgam B C)
      (sumAmalgamLinearLeft x) (sumAmalgamLinearLeft y) =
      indexedBananaPairing B x y := by
  classical
  simp [indexedBananaPairing, Fintype.sum_sum_type,
    sumAmalgamLinearLeft, bananaBlockAmalgam, mul_assoc]

/-- The second embedding also preserves the pairing when the two
matrices agree on their shared rectangle. -/
theorem indexedBananaPairing_amalgam_right
    {LA RA UB VB UC VC : Type*}
    [Fintype LA] [Fintype RA]
    [Fintype UB] [Fintype VB] [Fintype UC] [Fintype VC]
    (B : Matrix (Sum LA UB) (Sum RA VB) F2)
    (C : Matrix (Sum LA UC) (Sum RA VC) F2)
    (hcommon : ∀ a r, B (.inl a) (.inl r) = C (.inl a) (.inl r))
    (x : Sum LA UC → F2) (y : Sum RA VC → F2) :
    indexedBananaPairing (bananaBlockAmalgam B C)
      (sumAmalgamLinearRight x) (sumAmalgamLinearRight y) =
      indexedBananaPairing C x y := by
  classical
  simp [indexedBananaPairing, Fintype.sum_sum_type,
    sumAmalgamLinearRight, bananaBlockAmalgam, hcommon,
    mul_assoc]

/-- The two inclusions identify the chosen common coordinates
pointwise, on either vector-space sort. -/
theorem sumAmalgam_common_agrees
    {A X Y : Type*} (a : A → F2) :
    sumAmalgamLinearLeft (sumCommonLinear (X := X) a) =
      sumAmalgamLinearRight (sumCommonLinear (X := Y) a) := by
  exact (sumAmalgam_eq_iff_common
    (sumCommonLinear (X := X) a)
    (sumCommonLinear (X := Y) a)).2 ⟨a, rfl, rfl⟩

/-- An arbitrary finite split diagram of BANANA pairing matrices:
the old pairings have the same common left/right rectangle. -/
structure BananaSplitDiagram
    (LA RA UB VB UC VC : Type*) where
  B : Matrix (Sum LA UB) (Sum RA VB) F2
  C : Matrix (Sum LA UC) (Sum RA VC) F2
  common : ∀ a r, B (.inl a) (.inl r) = C (.inl a) (.inl r)

namespace BananaSplitDiagram

variable {LA RA UB VB UC VC : Type*}
variable [Fintype LA] [Fintype RA]
variable [Fintype UB] [Fintype VB] [Fintype UC] [Fintype VC]

/-- The block matrix of the canonical strong amalgam, with the two
unprescribed cross-pairings set to zero. -/
def amalgam (T : BananaSplitDiagram LA RA UB VB UC VC) :
    Matrix (Sum LA (Sum UB UC)) (Sum RA (Sum VB VC)) F2 :=
  bananaBlockAmalgam T.B T.C

/-- The first finite structure embeds into the amalgam. -/
theorem left_pairing (T : BananaSplitDiagram LA RA UB VB UC VC)
    (x : Sum LA UB → F2) (y : Sum RA VB → F2) :
    indexedBananaPairing T.amalgam
      (sumAmalgamLinearLeft x) (sumAmalgamLinearLeft y) =
    indexedBananaPairing T.B x y :=
  indexedBananaPairing_amalgam_left T.B T.C x y

/-- The second finite structure embeds into the amalgam. -/
theorem right_pairing (T : BananaSplitDiagram LA RA UB VB UC VC)
    (x : Sum LA UC → F2) (y : Sum RA VC → F2) :
    indexedBananaPairing T.amalgam
      (sumAmalgamLinearRight x) (sumAmalgamLinearRight y) =
    indexedBananaPairing T.C x y :=
  indexedBananaPairing_amalgam_right T.B T.C T.common x y

/-- The left and right sort injections are injective. -/
theorem left_sort_injective (T : BananaSplitDiagram LA RA UB VB UC VC) :
    Function.Injective
      (sumAmalgamLinearLeft :
        (Sum LA UB → F2) →ₗ[F2]
        (Sum LA (Sum UB UC) → F2)) :=
  sumAmalgamLinearLeft_injective

theorem right_sort_injective (T : BananaSplitDiagram LA RA UB VB UC VC) :
    Function.Injective
      (sumAmalgamLinearRight :
        (Sum LA UC → F2) →ₗ[F2]
        (Sum LA (Sum UB UC) → F2)) :=
  sumAmalgamLinearRight_injective

/-- Strong intersection on the left sort: the images have exactly
the common left-coordinate subspace in common. -/
theorem strong_left (T : BananaSplitDiagram LA RA UB VB UC VC)
    (x : Sum LA UB → F2) (y : Sum LA UC → F2) :
    sumAmalgamLinearLeft x = sumAmalgamLinearRight y ↔
      ∃ a : LA → F2,
        x = sumCommonLinear a ∧ y = sumCommonLinear a :=
  sumAmalgam_eq_iff_common x y

/-- The same strong intersection statement for the right sort. -/
theorem strong_right (T : BananaSplitDiagram LA RA UB VB UC VC)
    (x : Sum RA VB → F2) (y : Sum RA VC → F2) :
    sumAmalgamLinearLeft x = sumAmalgamLinearRight y ↔
      ∃ a : RA → F2,
        x = sumCommonLinear a ∧ y = sumCommonLinear a :=
  sumAmalgam_eq_iff_common x y

end BananaSplitDiagram

end SuccessorTree.NonPrecompact
