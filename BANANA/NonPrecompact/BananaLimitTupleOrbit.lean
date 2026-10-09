import BANANA.NonPrecompact.BananaLimitTupleKernelRange
import BANANA.NonPrecompact.BananaLimitTuplePairing
import BANANA.NonPrecompact.BananaLimitSubspaceHomogeneity

/-!
# Completeness of finite tuple signatures for the BANANA limit

Two pairs of finite tuples lie in the same orbit under the global
pairing-preserving automorphism group precisely when their linear
dependency data and cross-pairing tables agree. This module establishes
the hard direction: equal signatures imply a global automorphism
carrying one tuple to the other, coordinatewise on both sorts.

The proof uses equal coefficient-map kernels to identify the two
finite spans, bilinearity to preserve their induced pairing, and
intrinsic finite-subspace ultrahomogeneity to extend the isomorphism.
-/

namespace SuccessorTree.NonPrecompact

/-- The range of any linear map from a finite binary coordinate space
is a finite set, even if its ambient vector space is infinite. -/
theorem bananaLimitFiniteRange {n : ℕ}
    (f : (Fin n → F2) →ₗ[F2] BananaLimitVector) :
    Finite (LinearMap.range f) := by
  classical
  let ρ : (Fin n → F2) → LinearMap.range f :=
    fun c => ⟨f c, ⟨c, rfl⟩⟩
  apply Finite.of_surjective ρ
  rintro ⟨z, ⟨c, hc⟩⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  exact hc

/-- The finite tuple signature determines the complete global orbit
of ordered left and right tuples of the prescribed lengths. -/
theorem bananaLimitTupleSignature_complete {l r : ℕ}
    (a a' : Fin l → BananaLimitVector)
    (b b' : Fin r → BananaLimitVector)
    (h : bananaLimitTupleSignature a b =
      bananaLimitTupleSignature a' b') :
    ∃ EL ER : BananaLimitVector ≃ₗ[F2] BananaLimitVector,
      (∀ x y : BananaLimitVector,
        bananaLimitPairing (EL x) (ER y) = bananaLimitPairing x y) ∧
      (∀ i, EL (a i) = a' i) ∧
      (∀ j, ER (b j) = b' j) := by
  classical
  let la := bananaLimitTupleCombination a
  let la' := bananaLimitTupleCombination a'
  let rb := bananaLimitTupleCombination b
  let rb' := bananaLimitTupleCombination b'
  have hkerL : LinearMap.ker la = LinearMap.ker la' :=
    bananaLimitTupleSignature_eq_left_kernel a a' b b' h
  have hkerR : LinearMap.ker rb = LinearMap.ker rb' :=
    bananaLimitTupleSignature_eq_right_kernel a a' b b' h
  let fL : LinearMap.range la ≃ₗ[F2] LinearMap.range la' :=
    bananaLimitRangeEquivOfKernelEq la la' hkerL
  let fR : LinearMap.range rb ≃ₗ[F2] LinearMap.range rb' :=
    bananaLimitRangeEquivOfKernelEq rb rb' hkerR
  letI : Finite (LinearMap.range la) := bananaLimitFiniteRange la
  letI : Finite (LinearMap.range rb) := bananaLimitFiniteRange rb
  have hL (c : Fin l → F2) :
      (fL (⟨la c, ⟨c, rfl⟩⟩ : LinearMap.range la) :
        BananaLimitVector) = la' c :=
    bananaLimitRangeEquivOfKernelEq_apply la la' hkerL c
  have hR (d : Fin r → F2) :
      (fR (⟨rb d, ⟨d, rfl⟩⟩ : LinearMap.range rb) :
        BananaLimitVector) = rb' d :=
    bananaLimitRangeEquivOfKernelEq_apply rb rb' hkerR d
  have hEntry (i : Fin l) (j : Fin r) :
      bananaLimitPairing (a i) (b j) =
        bananaLimitPairing (a' i) (b' j) :=
    bananaLimitTupleSignature_eq_pairing a a' b b' h i j
  have hIsometry (u : LinearMap.range la) (v : LinearMap.range rb) :
      bananaLimitPairing (fL u : BananaLimitVector)
        (fR v : BananaLimitVector) =
      bananaLimitPairing (u : BananaLimitVector)
        (v : BananaLimitVector) := by
    obtain ⟨c, hc⟩ := u.property
    obtain ⟨d, hd⟩ := v.property
    have hu : (⟨la c, ⟨c, rfl⟩⟩ : LinearMap.range la) = u :=
      Subtype.ext hc
    have hv : (⟨rb d, ⟨d, rfl⟩⟩ : LinearMap.range rb) = v :=
      Subtype.ext hd
    rw [← hu, ← hv]
    change bananaLimitPairing
      (fL (⟨la c, ⟨c, rfl⟩⟩ : LinearMap.range la) : BananaLimitVector)
      (fR (⟨rb d, ⟨d, rfl⟩⟩ : LinearMap.range rb) : BananaLimitVector) =
      bananaLimitPairing (la c) (rb d)
    rw [hL c, hR d]
    exact (bananaLimitPairing_tupleCombinations_eq_of_entries
      a a' b b' hEntry c d).symm
  obtain ⟨EL, ER, hPair, hEL, hER⟩ :=
    bananaLimit_exists_global_pair_automorphism_extends_subspaces
      (LinearMap.range la) (LinearMap.range la')
      (LinearMap.range rb) (LinearMap.range rb')
      fL fR hIsometry
  refine ⟨EL, ER, hPair, ?_, ?_⟩
  · intro i
    let c : Fin l → F2 := Pi.single i 1
    have hci : la c = a i := bananaLimitTupleCombination_single a i
    have hci' : la' c = a' i := bananaLimitTupleCombination_single a' i
    calc
      EL (a i) = EL (la c) := congrArg EL hci.symm
      _ = (fL (⟨la c, ⟨c, rfl⟩⟩ : LinearMap.range la) :
            BananaLimitVector) := hEL (⟨la c, ⟨c, rfl⟩⟩ : LinearMap.range la)
      _ = la' c := hL c
      _ = a' i := hci'
  · intro j
    let d : Fin r → F2 := Pi.single j 1
    have hdj : rb d = b j := bananaLimitTupleCombination_single b j
    have hdj' : rb' d = b' j := bananaLimitTupleCombination_single b' j
    calc
      ER (b j) = ER (rb d) := congrArg ER hdj.symm
      _ = (fR (⟨rb d, ⟨d, rfl⟩⟩ : LinearMap.range rb) :
            BananaLimitVector) := hER (⟨rb d, ⟨d, rfl⟩⟩ : LinearMap.range rb)
      _ = rb' d := hR d
      _ = b' j := hdj'

end SuccessorTree.NonPrecompact
