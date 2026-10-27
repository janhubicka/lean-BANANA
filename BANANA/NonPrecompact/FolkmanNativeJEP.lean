import BANANA.NonPrecompact.FolkmanNativeStrongAmalgamPackage

/-!
# Joint embedding of finite Folkman--BANANA structures

The one-element zero Boolean ring is an initial object for
non-unital ring homomorphisms: its unique map to any Boolean ring is
injective.  With zero bilinear pairing on both base sorts, every
finite two-sort Folkman structure contains this common base.

Applying the verified finite strong-amalgamation construction to
those maps gives a joint embedding preserving both original pairings.
The use of non-unital embeddings is essential: there is no
corresponding initial nonzero unital ring for zero-ring targets.
-/

namespace SuccessorTree.NonPrecompact

/-- Additivity forces a pairing to vanish at the pair of zero elements. -/
theorem folkmanNativePairing_zero_zero
    {L R : Type*} [BooleanRing L] [BooleanRing R]
    (γ : L → R → F2)
    (hleft : ∀ x x' y, γ (x + x') y = γ x y + γ x' y) :
    γ (0 : L) (0 : R) = 0 := by
  have h := hleft (0 : L) (0 : L) (0 : R)
  have h' : (0 : F2) + γ (0 : L) (0 : R) =
      γ (0 : L) (0 : R) + γ (0 : L) (0 : R) := by
    simpa only [zero_add] using h
  exact (add_right_cancel h').symm

/-- Every two finite native Folkman structures jointly embed into a
single finite strong amalgam.  The common base has a zero ring in each
sort.  This theorem does not impose any unitality condition. -/
theorem folkmanNative_joint_embedding
    {BL BR CL CR : Type*}
    [BooleanRing BL] [Fintype BL]
    [BooleanRing BR] [Fintype BR]
    [BooleanRing CL] [Fintype CL]
    [BooleanRing CR] [Fintype CR]
    (γB : BL → BR → F2)
    (γC : CL → CR → F2)
    (hBleft : ∀ x x' y, γB (x + x') y = γB x y + γB x' y)
    (hCleft : ∀ x x' y, γC (x + x') y = γC x y + γC x' y)
    (hBright : ∀ x y y', γB x (y + y') = γB x y + γB x y')
    (hCright : ∀ x y y', γC x (y + y') = γC x y + γC x y') :
    Nonempty (FolkmanNativeStrongAmalgamCertificate
      (0 : PUnit →ₙ+* BL) (0 : PUnit →ₙ+* CL)
      (0 : PUnit →ₙ+* BR) (0 : PUnit →ₙ+* CR)
      γB γC) := by
  let γA : PUnit → PUnit → F2 := fun _ _ => 0
  have hAleft : ∀ x x' y,
      γA (x + x') y = γA x y + γA x' y := by
    intro x x' y
    simp [γA]
  have hAright : ∀ x y y',
      γA x (y + y') = γA x y + γA x y' := by
    intro x y y'
    simp [γA]
  have hzeroB : γB (0 : BL) (0 : BR) = 0 :=
    folkmanNativePairing_zero_zero γB hBleft
  have hzeroC : γC (0 : CL) (0 : CR) = 0 :=
    folkmanNativePairing_zero_zero γC hCleft
  refine folkmanNative_exists_language_strong_amalgam
    (0 : PUnit →ₙ+* BL) (0 : PUnit →ₙ+* CL)
    (0 : PUnit →ₙ+* BR) (0 : PUnit →ₙ+* CR)
    (by intro x y _; exact Subsingleton.elim x y)
    (by intro x y _; exact Subsingleton.elim x y)
    (by intro x y _; exact Subsingleton.elim x y)
    (by intro x y _; exact Subsingleton.elim x y)
    γA γB γC
    hAleft hBleft hCleft hAright hBright hCright
    ?_ ?_
  · intro a r
    simpa [γA] using hzeroB
  · intro a r
    simpa [γA] using hzeroC

end SuccessorTree.NonPrecompact
