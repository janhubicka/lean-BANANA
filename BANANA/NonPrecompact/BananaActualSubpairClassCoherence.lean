import BANANA.NonPrecompact.BananaActualSubpairFunctor

/-!
# A single coherent assignment on every actual BANANA subpair isomorphism class

The quotient atlas from BananaPresentedSubpairAtlas classifies presented finite
subpairs. Each actual substructure has a once-selected presentation and a
linear identification with each of its actual vector subspaces. We now pull
back the atlas's coherent family to ACTUAL subspace isomorphisms.

The main result covers every actual finite subpair, has one fixed ambient
witness B_(l+r), and proves extension, identities, composition and inverses
on each actual isomorphism class. No representative or conjugator data are
hypotheses of the theorem.

The final optional unindexed groupoid packaging (one map on arrows without
an explicit common class index) is separate, since quotient-index equality
requires a dependent transport. This is not a replacement for kernel checks.
-/

namespace SuccessorTree.NonPrecompact

/-- Actual subpairs whose fixed presentations lie in one pairing-isomorphism
class. The index is part of the type and is shared by any composable arrows. -/
abbrev BananaActualClassObject
    {l r : ℕ} (A : BananaMatrixStructure l r)
    (c : BananaPresentedIsoClass A) :=
  {U : BananaActualSubpair A // bananaPresentedClassOf U.presentation = c}

/-- The fixed presentation of an actual class object is in the corresponding
presentation class. No fresh representative is chosen. -/
def bananaActualClassObject_toPresented
    {l r : ℕ} {A : BananaMatrixStructure l r}
    {c : BananaPresentedIsoClass A} (U : BananaActualClassObject A c) :
    BananaPresentedClassObject A c :=
  ⟨U.1.presentation, U.2⟩

/-- Coordinate vector versus actual subpair vector after the common
perfect-completion embedding: both are literally the same ambient vector. -/
theorem BananaActualSubpair.left_completion_coordinate
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U : BananaActualSubpair A)
    (x : Fin U.presentation.leftDim → F2) :
    U.presentation.toPerfectCompletion.left x =
      A.completionEmbedding.left (U.leftCoordinateEquiv x).val := by
  change A.completionEmbedding.left (U.presentation.inclusion.left x) =
    A.completionEmbedding.left (U.leftCoordinateEquiv x).val
  rw [U.leftCoordinateEquiv_val]

/-- Right-sort analogue of the literal coordinate identification. -/
theorem BananaActualSubpair.right_completion_coordinate
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U : BananaActualSubpair A)
    (y : Fin U.presentation.rightDim → F2) :
    U.presentation.toPerfectCompletion.right y =
      A.completionEmbedding.right (U.rightCoordinateEquiv y).val := by
  change A.completionEmbedding.right (U.presentation.inclusion.right y) =
    A.completionEmbedding.right (U.rightCoordinateEquiv y).val
  rw [U.rightCoordinateEquiv_val]

/-- Complete coherent EPPA on actual finite subpairs, indexed by their
isomorphism classes. All arrows are actual two-sorted linear isomorphisms
preserving the restricted pairing; the group on the right is the ACTUAL
pairing-preserving automorphism group of the same perfect completion.

The only parameters are the original finite structure A and its dimensions.
The type index c is fixed for each composable pair, and the quotient atlas
ensures every actual partial isomorphism has endpoints in some such class. -/
theorem exists_bananaActualClassCoherentExtension
    {l r : ℕ} (A : BananaMatrixStructure l r) :
    ∃ Θ : ∀ (c : BananaPresentedIsoClass A)
        ⦃U V : BananaActualClassObject A c⦄,
        BananaActualSubpairIso U.1 V.1 →
          BananaMatrixAutGroup (perfectBanana (l + r)),
      (∀ (c : BananaPresentedIsoClass A)
          (U : BananaActualClassObject A c),
        Θ c (BananaActualSubpairIso.refl U.1) = 1) ∧
      (∀ (c : BananaPresentedIsoClass A)
          (U V W : BananaActualClassObject A c)
          (p : BananaActualSubpairIso U.1 V.1)
          (q : BananaActualSubpairIso V.1 W.1),
        Θ c q * Θ c p = Θ c (p.trans q)) ∧
      (∀ (c : BananaPresentedIsoClass A)
          (U V : BananaActualClassObject A c)
          (p : BananaActualSubpairIso U.1 V.1),
        (Θ c p)⁻¹ = Θ c p.symm) ∧
      (∀ (c : BananaPresentedIsoClass A)
          (U V : BananaActualClassObject A c)
          (p : BananaActualSubpairIso U.1 V.1),
        (∀ (x : U.1.left),
          (Θ c p).1.1 (A.completionEmbedding.left x.val) =
            A.completionEmbedding.left (p.left x).val) ∧
        (∀ (y : U.1.right),
          (Θ c p).1.2 (A.completionEmbedding.right y.val) =
            A.completionEmbedding.right (p.right y).val)) := by
  classical
  obtain ⟨Φ, hId, hComp, hInv, hExt⟩ :=
    exists_bananaPresentedClassCoherentExtension A
  let O : BananaPresentedIsoClass A → Type := BananaActualClassObject A
  let F (c : BananaPresentedIsoClass A) (U : O c) :
      BananaPresentedClassObject A c := bananaActualClassObject_toPresented U
  let Θ : ∀ (c : BananaPresentedIsoClass A) ⦃U V : O c⦄,
      BananaActualSubpairIso U.1 V.1 →
        BananaMatrixAutGroup (perfectBanana (l + r)) :=
    fun c {U V} p =>
      Φ c (U := F c U) (V := F c V) p.toPresentedIso
  refine ⟨Θ, ?_, ?_, ?_, ?_⟩
  · intro c U
    change Φ c ((BananaActualSubpairIso.refl U.1).toPresentedIso) = 1
    rw [BananaActualSubpairIso.toPresentedIso_refl]
    exact hId c (F c U)
  · intro c U V W p q
    change Φ c q.toPresentedIso * Φ c p.toPresentedIso =
      Φ c ((p.trans q).toPresentedIso)
    rw [BananaActualSubpairIso.toPresentedIso_trans]
    exact hComp c (F c U) (F c V) (F c W) p.toPresentedIso q.toPresentedIso
  · intro c U V p
    change (Φ c p.toPresentedIso)⁻¹ = Φ c p.symm.toPresentedIso
    rw [BananaActualSubpairIso.toPresentedIso_symm]
    exact hInv c (F c U) (F c V) p.toPresentedIso
  · intro c U V p
    obtain ⟨hL, hR⟩ := hExt c (F c U) (F c V) p.toPresentedIso
    constructor
    · intro x
      obtain ⟨z, hz⟩ := U.1.leftCoordinateEquiv.surjective x
      subst x
      change (Φ c p.toPresentedIso).1.1
        (A.completionEmbedding.left (U.1.leftCoordinateEquiv z).val) =
        A.completionEmbedding.left (p.left (U.1.leftCoordinateEquiv z)).val
      calc
        (Φ c p.toPresentedIso).1.1
            (A.completionEmbedding.left (U.1.leftCoordinateEquiv z).val) =
            (Φ c p.toPresentedIso).1.1
              (U.1.presentation.toPerfectCompletion.left z) := by
                rw [U.1.left_completion_coordinate]
        _ = V.1.presentation.toPerfectCompletion.left
              (p.toPresentedIso.left z) := hL z
        _ = A.completionEmbedding.left
              (V.1.leftCoordinateEquiv (p.toPresentedIso.left z)).val :=
                V.1.left_completion_coordinate _
        _ = A.completionEmbedding.left
              (p.left (U.1.leftCoordinateEquiv z)).val := by
                rw [p.toPresentedIso_left_coordinates]
    · intro y
      obtain ⟨z, hz⟩ := U.1.rightCoordinateEquiv.surjective y
      subst y
      change (Φ c p.toPresentedIso).1.2
        (A.completionEmbedding.right (U.1.rightCoordinateEquiv z).val) =
        A.completionEmbedding.right (p.right (U.1.rightCoordinateEquiv z)).val
      calc
        (Φ c p.toPresentedIso).1.2
            (A.completionEmbedding.right (U.1.rightCoordinateEquiv z).val) =
            (Φ c p.toPresentedIso).1.2
              (U.1.presentation.toPerfectCompletion.right z) := by
                rw [U.1.right_completion_coordinate]
        _ = V.1.presentation.toPerfectCompletion.right
              (p.toPresentedIso.right z) := hR z
        _ = A.completionEmbedding.right
              (V.1.rightCoordinateEquiv (p.toPresentedIso.right z)).val :=
                V.1.right_completion_coordinate _
        _ = A.completionEmbedding.right
              (p.right (U.1.rightCoordinateEquiv z)).val := by
                rw [p.toPresentedIso_right_coordinates]

end SuccessorTree.NonPrecompact
