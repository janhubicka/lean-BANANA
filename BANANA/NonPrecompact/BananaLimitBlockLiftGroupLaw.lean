import BANANA.NonPrecompact.BananaLimitBlockPairLift

/-!
# Composition of finite-block lifts on the BANANA limit

The extension by the identity outside a finite coordinate set is
compatible with identity and composition of block automorphisms.

Together with the finite cardinality of each block GL group, these
lemmas prepare the proof that the lifted finite stages form genuine
finite subgroups of the automorphism group of the countable pairing.
-/

namespace SuccessorTree.NonPrecompact

/-- Extending the identity map of a finite block gives the global
identity linear automorphism. -/
theorem bananaLimitBlockLift_refl (S : Finset ℚ) :
    bananaLimitBlockLift S
      (LinearEquiv.refl F2 (bananaLimitBlock S)) =
      LinearEquiv.refl F2 BananaLimitVector := by
  apply LinearEquiv.ext
  intro x
  change bananaLimitBlockLift S
    (LinearEquiv.refl F2 (bananaLimitBlock S)) x = x
  rw [bananaLimitBlockLift_apply]
  change (bananaLimitFinitePart S x : BananaLimitVector) +
    bananaLimitOutsidePart S x = x
  exact bananaLimit_finite_outside_decomposition S x

/-- Extending two block transformations and composing globally is
the same as extending their composition on the finite block. -/
theorem bananaLimitBlockLift_trans
    (S : Finset ℚ)
    (f g : bananaLimitBlock S ≃ₗ[F2] bananaLimitBlock S) :
    bananaLimitBlockLift S (f.trans g) =
      (bananaLimitBlockLift S f).trans
        (bananaLimitBlockLift S g) := by
  apply LinearEquiv.ext
  intro x
  change bananaLimitBlockLift S (f.trans g) x =
    bananaLimitBlockLift S g (bananaLimitBlockLift S f x)
  symm
  calc
    bananaLimitBlockLift S g (bananaLimitBlockLift S f x) =
        bananaLimitBlockLift S g
          ((f (bananaLimitFinitePart S x) : BananaLimitVector) +
            bananaLimitOutsidePart S x) :=
          congrArg (bananaLimitBlockLift S g)
            (bananaLimitBlockLift_apply S f x)
    _ = (g (f (bananaLimitFinitePart S x)) : BananaLimitVector) +
          bananaLimitOutsidePart S x := by
          rw [map_add, bananaLimitBlockLift_on_block,
            bananaLimitBlockLift_on_outside]
    _ = bananaLimitBlockLift S (f.trans g) x := by
          rw [bananaLimitBlockLift_apply]
          rfl

end SuccessorTree.NonPrecompact
