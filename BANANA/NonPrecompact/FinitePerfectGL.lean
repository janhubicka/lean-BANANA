import BANANA.NonPrecompact.CompletionAmbientAction
import Mathlib.Data.Fintype.Basic

/-!
# Finite perfect-pair automorphisms and standard block extensions

The finite subgroups used in the circulation proof of amenability are
parametrised by the invertible linear maps on a finite binary coordinate
space. The action on the other sort is uniquely prescribed by the
contragredient, so each parameter gives an automorphism of the standard
perfect pairing.

Here we formalise the finite parameter family and the compatible
block-diagonal extension obtained by fixing extra coordinates. These
are the finite algebraic ingredients of the locally finite dense
subgroup; density in the countable limit and topological amenability
are separate obligations, not claimed by this module.
-/

namespace SuccessorTree.NonPrecompact

/-- The general linear group, regarded here as a finite type of linear
equivalences rather than as a separately packaged abstract group. -/
abbrev FinitePerfectGL (n : ℕ) :=
  (Fin n → F2) ≃ₗ[F2] (Fin n → F2)

/-- In finite dimension over F₂, there are only finitely many
invertible linear maps. -/
instance finitePerfectGLFinite (n : ℕ) : Finite (FinitePerfectGL n) := by
  classical
  let evalMap : FinitePerfectGL n →
      ((Fin n → F2) → (Fin n → F2)) := fun h => h
  have heval : Function.Injective evalMap := by
    intro f g h
    apply LinearEquiv.ext
    intro x
    exact congrFun h x
  exact Finite.of_injective evalMap heval

/-- Realise each invertible left linear map as a pairing-preserving
automorphism of the finite standard perfect BANANA structure. -/
noncomputable def FinitePerfectGL.toPerfectPairAutomorphism
    {n : ℕ} (h : FinitePerfectGL n) :
    BananaMatrixEmbedding (perfectBanana n) (perfectBanana n) :=
  perfectPairAutomorphismOfLinearEquiv h

/-- The perfect pairing is preserved under the induced left/right
automorphism. -/
theorem FinitePerfectGL.pairing_preserved
    {n : ℕ} (h : FinitePerfectGL n)
    (x y : Fin n → F2) :
    (perfectBanana n).eval
        (h.toPerfectPairAutomorphism.left x)
        (h.toPerfectPairAutomorphism.right y) =
      (perfectBanana n).eval x y :=
  h.toPerfectPairAutomorphism.pairing_apply x y

/-- Extend an invertible coordinate transformation by the identity
on an adjoining finite coordinate block. -/
noncomputable def finitePerfectGLBlockLift
    (n k : ℕ) (h : FinitePerfectGL n) :
    FinitePerfectGL (n + k) :=
  BananaMatrixStructure.directSumLinearEquiv h
    (LinearEquiv.refl F2 (Fin k → F2))

/-- The extension agrees with the original linear map on the old
coordinates. -/
theorem finitePerfectGLBlockLift_first
    (n k : ℕ) (h : FinitePerfectGL n) (x : Fin n → F2) :
    finitePerfectGLBlockLift n k h (Fin.append x 0) =
      Fin.append (h x) 0 := by
  rw [finitePerfectGLBlockLift,
    BananaMatrixStructure.directSumLinearEquiv_apply]
  simp

/-- The extension is the identity on the new coordinates. -/
theorem finitePerfectGLBlockLift_second
    (n k : ℕ) (h : FinitePerfectGL n) (z : Fin k → F2) :
    finitePerfectGLBlockLift n k h (Fin.append 0 z) =
      Fin.append 0 z := by
  rw [finitePerfectGLBlockLift,
    BananaMatrixStructure.directSumLinearEquiv_apply]
  simp

/-- Extending the identity transformation gives the identity. -/
theorem finitePerfectGLBlockLift_refl (n k : ℕ) :
    finitePerfectGLBlockLift n k
        (LinearEquiv.refl F2 (Fin n → F2)) =
      LinearEquiv.refl F2 (Fin (n + k) → F2) := by
  exact BananaMatrixStructure.directSumLinearEquiv_refl

/-- Extension respects the composition of finite coordinate
transformations. -/
theorem finitePerfectGLBlockLift_trans
    (n k : ℕ) (f g : FinitePerfectGL n) :
    finitePerfectGLBlockLift n k (f.trans g) =
      (finitePerfectGLBlockLift n k f).trans
        (finitePerfectGLBlockLift n k g) := by
  exact BananaMatrixStructure.directSumLinearEquiv_trans
    f g
    (LinearEquiv.refl F2 (Fin k → F2))
    (LinearEquiv.refl F2 (Fin k → F2))

/-- The block extension is injective: its action on the first block
recovers the original transformation. -/
theorem finitePerfectGLBlockLift_injective
    (n k : ℕ) :
    Function.Injective (finitePerfectGLBlockLift n k) := by
  intro f g h
  apply LinearEquiv.ext
  intro x
  have hx := congrArg
    (fun u : FinitePerfectGL (n + k) => u (Fin.append x 0)) h
  rw [finitePerfectGLBlockLift_first,
    finitePerfectGLBlockLift_first] at hx
  exact (Fin.append_injective hx).1

/-- The induced automorphism fixes the added left coordinates. -/
theorem finitePerfectGLBlockLift_automorphism_left_complement
    (n k : ℕ) (h : FinitePerfectGL n) (z : Fin k → F2) :
    (finitePerfectGLBlockLift n k h).toPerfectPairAutomorphism.left
        (Fin.append 0 z) =
      Fin.append 0 z :=
  finitePerfectGLBlockLift_second n k h z

/-- The right action of the block automorphism is the original
contragredient on the first block. -/
theorem finitePerfectGLBlockLift_automorphism_right_first
    (n k : ℕ) (h : FinitePerfectGL n) (y : Fin n → F2) :
    (finitePerfectGLBlockLift n k h).toPerfectPairAutomorphism.right
        (Fin.append y 0) =
      Fin.append (dotContragredient h y) 0 := by
  change dotContragredient (finitePerfectGLBlockLift n k h)
      (Fin.append y 0) = _
  rw [finitePerfectGLBlockLift,
    BananaMatrixStructure.dotContragredient_directSumLinearEquiv,
    dotContragredient_refl,
    BananaMatrixStructure.directSumLinearEquiv_apply]
  simp

/-- The induced right action also fixes every new coordinate. -/
theorem finitePerfectGLBlockLift_automorphism_right_complement
    (n k : ℕ) (h : FinitePerfectGL n) (z : Fin k → F2) :
    (finitePerfectGLBlockLift n k h).toPerfectPairAutomorphism.right
        (Fin.append 0 z) =
      Fin.append 0 z := by
  change dotContragredient (finitePerfectGLBlockLift n k h)
      (Fin.append 0 z) = _
  rw [finitePerfectGLBlockLift,
    BananaMatrixStructure.dotContragredient_directSumLinearEquiv,
    dotContragredient_refl,
    BananaMatrixStructure.directSumLinearEquiv_apply]
  simp

end SuccessorTree.NonPrecompact
