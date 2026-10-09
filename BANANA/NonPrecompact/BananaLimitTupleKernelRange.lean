import BANANA.NonPrecompact.BananaLimitTupleSignatures
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Recovering finite subspaces from BANANA tuple signatures

Equality of signatures is equivalent to agreement of the kernels of
the coefficient-to-vector maps, separately on both sorts, together
with agreement of the cross-pairing table.

The first isomorphism theorem then identifies the two spans of each
sort via the same coefficient vectors. Later the bilinearity of the
pairing will be used to show that these two equivalences preserve all
cross-pairings, so finite-subspace ultrahomogeneity applies.
-/

namespace SuccessorTree.NonPrecompact

/-- Equal signatures give exactly the same left linear relations. -/
theorem bananaLimitTupleSignature_eq_left_relations
    {l r : ℕ}
    (a a' : Fin l → BananaLimitVector)
    (b b' : Fin r → BananaLimitVector)
    (h : bananaLimitTupleSignature a b =
      bananaLimitTupleSignature a' b')
    (c : Fin l → F2) :
    bananaLimitTupleCombination a c = 0 ↔
      bananaLimitTupleCombination a' c = 0 := by
  have hc := congrArg
    (fun s : BananaLimitTupleSignature l r => s.1 c) h
  calc
    bananaLimitTupleCombination a c = 0 ↔
        (bananaLimitTupleSignature a b).1 c = true :=
      (bananaLimitTupleSignature_left_relation a b c).symm
    _ ↔ (bananaLimitTupleSignature a' b').1 c = true := by
      rw [hc]
    _ ↔ bananaLimitTupleCombination a' c = 0 :=
      bananaLimitTupleSignature_left_relation a' b' c

/-- Equal signatures give exactly the same right linear relations. -/
theorem bananaLimitTupleSignature_eq_right_relations
    {l r : ℕ}
    (a a' : Fin l → BananaLimitVector)
    (b b' : Fin r → BananaLimitVector)
    (h : bananaLimitTupleSignature a b =
      bananaLimitTupleSignature a' b')
    (d : Fin r → F2) :
    bananaLimitTupleCombination b d = 0 ↔
      bananaLimitTupleCombination b' d = 0 := by
  have hd := congrArg
    (fun s : BananaLimitTupleSignature l r => s.2.1 d) h
  calc
    bananaLimitTupleCombination b d = 0 ↔
        (bananaLimitTupleSignature a b).2.1 d = true :=
      (bananaLimitTupleSignature_right_relation a b d).symm
    _ ↔ (bananaLimitTupleSignature a' b').2.1 d = true := by
      rw [hd]
    _ ↔ bananaLimitTupleCombination b' d = 0 :=
      bananaLimitTupleSignature_right_relation a' b' d

/-- Equal signatures give the same pairing of corresponding entries. -/
theorem bananaLimitTupleSignature_eq_pairing
    {l r : ℕ}
    (a a' : Fin l → BananaLimitVector)
    (b b' : Fin r → BananaLimitVector)
    (h : bananaLimitTupleSignature a b =
      bananaLimitTupleSignature a' b')
    (i : Fin l) (j : Fin r) :
    bananaLimitPairing (a i) (b j) =
      bananaLimitPairing (a' i) (b' j) := by
  have hp := congrArg
    (fun s : BananaLimitTupleSignature l r => s.2.2 i j) h
  simpa only [bananaLimitTupleSignature_pairing] using hp

/-- Left coefficient maps have equal kernels when signatures agree. -/
theorem bananaLimitTupleSignature_eq_left_kernel
    {l r : ℕ}
    (a a' : Fin l → BananaLimitVector)
    (b b' : Fin r → BananaLimitVector)
    (h : bananaLimitTupleSignature a b =
      bananaLimitTupleSignature a' b') :
    LinearMap.ker (bananaLimitTupleCombination a) =
      LinearMap.ker (bananaLimitTupleCombination a') := by
  apply Submodule.ext
  intro c
  simpa only [LinearMap.mem_ker] using
    bananaLimitTupleSignature_eq_left_relations a a' b b' h c

/-- Right coefficient maps have equal kernels when signatures agree. -/
theorem bananaLimitTupleSignature_eq_right_kernel
    {l r : ℕ}
    (a a' : Fin l → BananaLimitVector)
    (b b' : Fin r → BananaLimitVector)
    (h : bananaLimitTupleSignature a b =
      bananaLimitTupleSignature a' b') :
    LinearMap.ker (bananaLimitTupleCombination b) =
      LinearMap.ker (bananaLimitTupleCombination b') := by
  apply Submodule.ext
  intro d
  simpa only [LinearMap.mem_ker] using
    bananaLimitTupleSignature_eq_right_relations a a' b b' h d

/-- Two linear maps with the same kernel have naturally linearly
equivalent ranges, via their common quotient by that kernel. -/
noncomputable def bananaLimitRangeEquivOfKernelEq {n : ℕ}
    (f g : (Fin n → F2) →ₗ[F2] BananaLimitVector)
    (h : LinearMap.ker f = LinearMap.ker g) :
    LinearMap.range f ≃ₗ[F2] LinearMap.range g :=
  ((f.quotKerEquivRange.symm.trans
      (Submodule.quotEquivOfEq (LinearMap.ker f) (LinearMap.ker g) h)).trans
    g.quotKerEquivRange)

/-- The resulting equivalence sends each combination to the same
combination of vectors on the other side, not just to an arbitrary
vector of the correct span. -/
theorem bananaLimitRangeEquivOfKernelEq_apply {n : ℕ}
    (f g : (Fin n → F2) →ₗ[F2] BananaLimitVector)
    (h : LinearMap.ker f = LinearMap.ker g)
    (c : Fin n → F2) :
    (bananaLimitRangeEquivOfKernelEq f g h
      (⟨f c, ⟨c, rfl⟩⟩ : LinearMap.range f) :
        BananaLimitVector) = g c := by
  classical
  let u : LinearMap.range f := ⟨f c, ⟨c, rfl⟩⟩
  have hpre :
      f.quotKerEquivRange.symm u = (LinearMap.ker f).mkQ c := by
    exact LinearMap.quotKerEquivRange_symm_apply_image
      f c (show f c ∈ LinearMap.range f from ⟨c, rfl⟩)
  change ((g.quotKerEquivRange
    ((Submodule.quotEquivOfEq (LinearMap.ker f) (LinearMap.ker g) h)
      (f.quotKerEquivRange.symm u))) :
      BananaLimitVector) = g c
  rw [hpre]
  simp

end SuccessorTree.NonPrecompact
