import BANANA.NonPrecompact.LinearBinaryComposition
import BANANA.NonPrecompact.LinearBinaryExactCoordinates
import BANANA.NonPrecompact.BinarySubspaceRamseyFromSuccessor

/-!
# The remaining range-representation interface for binary GLR

For the linear binary successor-tree instance, the factorisation field of
`BinarySubspaceSuccessorEncoding` follows from one property: every finite
binary subspace can be represented as the range of an exact successor
approximation.

The pullback argument is elementary linear algebra. Given a source subspace
P inside the range of an injective linear map φ, the comap of P under φ has
the same dimension as P, and mapping the comap back under φ recovers P.
Our verified exact-composition identity then identifies the resulting
successor-coordinate range with P.

No binary GLR theorem is postulated here. The only argument below is the
concrete range-surjectivity property.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

open Module

/-- The sole remaining representation statement needed for the binary
successor-to-GLR transfer: every fixed-dimensional binary subspace is
realised by an exact finite linear binary successor approximation. -/
def EveryBinarySubspaceRepresentable : Prop :=
  ∀ (d N : ℕ) (P : FixedSubspace d N),
    ∃ f : SMTree.AM.At linearBinarySMTree 0 (d + 1) N,
      exactSubspace f = P

/-- Every zero-dimensional subspace has an exact successor
representation, including at ambient level zero. -/
theorem exactSubspace_representable_zero
    (N : ℕ) (P : FixedSubspace 0 N) :
    ∃ f : SMTree.AM.At linearBinarySMTree 0 (0 + 1) N,
      exactSubspace f = P := by
  let f := zeroPaddingExact 0 N (Nat.zero_le N)
  refine ⟨f, ?_⟩
  apply Subtype.ext
  have hP : P.1 = ⊥ :=
    Submodule.finrank_eq_zero.mp P.2
  have hf : (exactSubspace f).1 = ⊥ :=
    Submodule.finrank_eq_zero.mp (exactSubspace f).2
  exact hf.trans hP.symm

/-- An exact successor approximation can represent the full ambient
space. This is the other boundary case of the pivot induction. -/
theorem exactSubspace_representable_full
    (N : ℕ) (P : FixedSubspace N N) :
    ∃ f : SMTree.AM.At linearBinarySMTree 0 (N + 1) N,
      exactSubspace f = P := by
  let f := zeroPaddingExact N N le_rfl
  refine ⟨f, ?_⟩
  apply Subtype.ext
  have hambient :
      finrank F2 (Fin N → F2) = N := by
    simp [Module.finrank_fintype_fun_eq_card]
  have hP : P.1 = ⊤ :=
    Submodule.eq_top_of_finrank_eq (P.2.trans hambient.symm)
  have hf : (exactSubspace f).1 = ⊤ :=
    Submodule.eq_top_of_finrank_eq
      ((exactSubspace f).2.trans hambient.symm)
  exact hf.trans hP.symm

/-- The exact finite successor encoding, conditional only on range
surjectivity. The M1-M3 structure, exact composition on ranges, and
nonemptiness of finite coordinate classes are all constructed separately. -/
noncomputable def binarySuccessorEncoding_of_representable
    (hrep : EveryBinarySubspaceRepresentable) :
    BinarySubspaceSuccessorEncoding linearBinarySMTree where
  toSubspace := fun {d N} f => exactSubspace f
  coordinate_nonempty := by
    intro a D haD
    exact exactCoordinate_nonempty haD
  factor := by
    intro a D N haD f P hPf
    let φ : (Fin D → F2) →ₗ[F2] (Fin N → F2) :=
      (exactLinearModel f).map
    have hφ : Function.Injective φ :=
      exactLinearModel_injective f
    have hle : P.1 ≤ LinearMap.range φ := by
      exact hPf
    let Q : Submodule F2 (Fin D → F2) :=
      P.1.comap φ
    have hmap : Q.map φ = P.1 :=
      Submodule.map_comap_eq_of_le hle
    have hdim : finrank F2 Q = a := by
      calc
        finrank F2 Q =
            finrank F2 (Q.map φ) :=
          (Submodule.equivMapOfInjective φ hφ Q).finrank_eq
        _ = finrank F2 P.1 := by rw [hmap]
        _ = a := P.2
    let Qfix : FixedSubspace a D := ⟨Q, hdim⟩
    obtain ⟨g, hg⟩ := hrep a D Qfix
    refine ⟨g, ?_⟩
    apply Subtype.ext
    have hgval : (exactSubspace g).1 = Q := by
      exact congrArg Subtype.val hg
    calc
      (exactSubspace
        (SMTree.exactComp linearBinarySMTree
          (by omega : 0 < D + 1)
          (by omega : 0 < a + 1)
          f g)).1 =
          Submodule.map φ (exactSubspace g).1 :=
        exactSubspace_comp f g
      _ = Q.map φ := by rw [hgval]
      _ = P.1 := hmap

/-- With range-surjectivity as the only additional hypothesis, the
finite successor theorem proves binary GLR, hence the one-sided BANANA
degree-one conclusions. -/
theorem binarySubspaceRamsey_of_representable
    (hrep : EveryBinarySubspaceRepresentable) :
    BinarySubspaceRamsey :=
  binarySubspaceRamsey_of_successorEncoding linearBinarySMTree
    (binarySuccessorEncoding_of_representable hrep)

theorem leftOneSidedCopyRamseyOne_of_representable
    (hrep : EveryBinarySubspaceRepresentable) (a : ℕ) :
    LeftOneSidedCopyRamseyOne a :=
  leftOneSidedCopyRamseyOne_of_binarySubspaceRamsey
    (binarySubspaceRamsey_of_representable hrep) a

theorem rightOneSidedCopyRamseyOne_of_representable
    (hrep : EveryBinarySubspaceRepresentable) (a : ℕ) :
    RightOneSidedCopyRamseyOne a :=
  rightOneSidedCopyRamseyOne_of_binarySubspaceRamsey
    (binarySubspaceRamsey_of_representable hrep) a

end BinaryWord
end SuccessorTree.NonPrecompact
