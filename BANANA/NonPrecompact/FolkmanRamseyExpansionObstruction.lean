import BANANA.NonPrecompact.FolkmanNativeCopySystem
import BANANA.NonPrecompact.FolkmanNativeCopyTransport
import BANANA.NonPrecompact.FolkmanNativeOneAtom

/-!
# The Folkman–BANANA Ramsey expansion obstruction

The native persistent colouring is transferred to the actual pairs of
copy ranges. The common copy-degree bound for precompact Ramsey
expansions then applies directly to this class.
-/

namespace SuccessorTree.NonPrecompact

open FolkmanNativeFiniteModel

/-- The standard `B_folk(q)` on the two diagonal families of `q` atoms. -/
noncomputable def folkmanNativeDiagonal (q : ℕ) : FolkmanNativeFiniteModel where
  Left := FolkmanNativeCodeRing q
  Right := FolkmanNativeCodeRing q
  pairing := folkmanNativeCodeRealisation (FolkmanAtomStructure.diagonal q)

private theorem source_pairing_one : (folkmanNativeDiagonal 1).pairing.pairing 1 1 = 1 := by
  have h : ({0} : Finset (Fin 1)) = Finset.univ := by
    ext i
    simp [Subsingleton.elim i 0]
  have hedge : (FolkmanAtomStructure.diagonal 1).edge (0 : Fin 1) (0 : Fin 1) = 1 := by
    change (if (0 : Fin 1) = 0 then (1 : F2) else 0) = 1
    exact ite_eq_left rfl
  have hp : (folkmanNativeCodeRealisation (FolkmanAtomStructure.diagonal 1)).pairing
      (toBoolRing ({0} : Finset (Fin 1))) (toBoolRing ({0} : Finset (Fin 1))) = 1 :=
    (folkmanNativeCodeRealisation_singletons (FolkmanAtomStructure.diagonal 1)
      (0 : Fin 1) (0 : Fin 1)).trans hedge
  change (folkmanNativeCodeRealisation (FolkmanAtomStructure.diagonal 1)).pairing
    (toBoolRing (Finset.univ : Finset (Fin 1))) (toBoolRing (Finset.univ : Finset (Fin 1))) = 1
  simpa only [h] using hp

private theorem pairing_zero_left {L R : Type*} [BooleanRing L] [BooleanRing R]
    (P : FolkmanNativeFinitePairing L R) (y : R) : P.pairing 0 y = 0 := by
  have h := P.add_left 0 0 y
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

private theorem pairing_zero_right {L R : Type*} [BooleanRing L] [BooleanRing R]
    (P : FolkmanNativeFinitePairing L R) (x : L) : P.pairing x 0 = 0 := by
  have h := P.add_right x 0 0
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

private noncomputable def embedSource {C : FolkmanNativeFiniteModel}
    (X : FolkmanNativeAxCopy C.pairing) : Embedding (folkmanNativeDiagonal 1) C where
  left := folkmanOneAtomHom X.left
  right := folkmanOneAtomHom X.right
  left_injective := folkmanOneAtomHom_injective X.left_ne_zero
  right_injective := folkmanOneAtomHom_injective X.right_ne_zero
  preserves_pairing := by
    intro a b
    change C.pairing.pairing (folkmanOneAtomHom X.left a) (folkmanOneAtomHom X.right b) =
      (folkmanNativeDiagonal 1).pairing.pairing a b
    rcases folkmanOneAtom_eq_zero_or_one a with rfl | rfl <;>
      rcases folkmanOneAtom_eq_zero_or_one b with rfl | rfl <;>
      simp only [map_zero, folkmanOneAtomHom_one]
    · exact (pairing_zero_left C.pairing _).trans
        (pairing_zero_left (folkmanNativeDiagonal 1).pairing _).symm
    · exact (pairing_zero_left C.pairing _).trans
        (pairing_zero_left (folkmanNativeDiagonal 1).pairing _).symm
    · exact (pairing_zero_right C.pairing _).trans
        (pairing_zero_right (folkmanNativeDiagonal 1).pairing _).symm
    · exact X.pairing_one.trans source_pairing_one.symm

private theorem embedSource_ranges {C : FolkmanNativeFiniteModel}
    (X : FolkmanNativeAxCopy C.pairing) :
    (Copy.ofEmbedding (embedSource X)).val = ({0, X.left}, {0, X.right}) := by
  apply Prod.ext
  · change Set.range (folkmanOneAtomHom X.left) = _
    exact (folkmanOneAtomHom_range (folkmanOneAtomHom X.left)).trans
      (congrArg (fun x => ({0, x} : Set C.Left)) (folkmanOneAtomHom_one X.left))
  · change Set.range (folkmanOneAtomHom X.right) = _
    exact (folkmanOneAtomHom_range (folkmanOneAtomHom X.right)).trans
      (congrArg (fun x => ({0, x} : Set C.Right)) (folkmanOneAtomHom_one X.right))

/-- Pairing-one generators parametrise exactly the unlabelled copies of
the canonical source `A_folk = B_folk(1)` on the original carriers. -/
noncomputable def folkmanNativeSourceCopyEquiv (C : FolkmanNativeFiniteModel) :
    FolkmanNativeAxCopy C.pairing ≃ Copy (folkmanNativeDiagonal 1) C := by
  refine Equiv.ofBijective (fun X => Copy.ofEmbedding (embedSource X)) ⟨?_, ?_⟩
  · intro X Y h
    have he := (embedSource_ranges X).symm.trans ((congrArg Subtype.val h).trans
      (embedSource_ranges Y))
    have hleft : X.left = Y.left := by
      have hL : ({0, X.left} : Set C.Left) = {0, Y.left} := congrArg Prod.fst he
      have hm : X.left ∈ ({0, Y.left} : Set C.Left) := hL ▸
        (Set.mem_insert_of_mem 0 (Set.mem_singleton X.left))
      exact Set.mem_singleton_iff.mp ((Set.mem_insert_iff.mp hm).resolve_left X.left_ne_zero)
    have hright : X.right = Y.right := by
      have hR : ({0, X.right} : Set C.Right) = {0, Y.right} := congrArg Prod.snd he
      have hm : X.right ∈ ({0, Y.right} : Set C.Right) := hR ▸
        (Set.mem_insert_of_mem 0 (Set.mem_singleton X.right))
      exact Set.mem_singleton_iff.mp ((Set.mem_insert_iff.mp hm).resolve_left X.right_ne_zero)
    cases X
    cases Y
    cases hleft
    cases hright
    rfl
  · intro p
    obtain ⟨f, hf⟩ := p.property
    let X : FolkmanNativeAxCopy C.pairing :=
      ⟨f.left 1, f.right 1, (f.preserves_pairing 1 1).trans source_pairing_one⟩
    refine ⟨X, Subtype.ext ((embedSource_ranges X).trans (?_ : _ = p.val))⟩
    exact (Prod.ext (folkmanOneAtomHom_range f.left).symm (folkmanOneAtomHom_range f.right).symm).trans hf

/-- One colouring of the original copy ranges in an arbitrary ambient
structure attains all colours inside every diagonal target copy. -/
theorem exists_folkmanNativeCopyRangeColouring (k : ℕ) (C : FolkmanNativeFiniteModel) :
    ∃ colouring : Copy (folkmanNativeDiagonal 1) C → Fin (2 ^ k),
      ∀ f : Embedding (folkmanNativeDiagonal (2 ^ (k + 1))) C,
        ∀ colour : Fin (2 ^ k), ∃ p : Copy (folkmanNativeDiagonal 1) C,
          colouring p = colour ∧ p.val.1 ⊆ Set.range f.left ∧ p.val.2 ⊆ Set.range f.right := by
  let e := folkmanNativeSourceCopyEquiv C
  obtain ⟨colouring, hc⟩ := exists_folkmanNativePersistentColouring k C.pairing
  refine ⟨fun p => colouring (e.symm p), fun f colour => ?_⟩
  obtain ⟨X, hL, hR, hX⟩ := hc f colour
  refine ⟨e X, (congrArg colouring (e.symm_apply_apply X)).trans hX, ?_⟩
  change (Copy.ofEmbedding (embedSource X)).val.1 ⊆ Set.range f.left ∧
    (Copy.ofEmbedding (embedSource X)).val.2 ⊆ Set.range f.right
  rw [embedSource_ranges]
  exact ⟨hL, hR⟩

/-- The native canonical source has infinite copy Ramsey degree. -/
theorem folkmanNativeCopyRamseyDegree_infinite (t : ℕ) :
    ¬ folkmanNativeCopySystem.CopyRamseyDegreeLE (folkmanNativeDiagonal 1) t := by
  classical
  let _ := folkmanNativeCopySystem.copyFintype (folkmanNativeDiagonal 1)
    (folkmanNativeDiagonal (2 ^ (t + 1)))
  intro h
  obtain ⟨C, hC⟩ := h (folkmanNativeDiagonal (2 ^ (t + 1))) (2 ^ t) (by positivity)
  obtain ⟨colouring, hcolouring⟩ := exists_folkmanNativeCopyRangeColouring t C
  obtain ⟨f, hf⟩ := hC colouring
  have hall : folkmanNativeCopySystem.coloursInside colouring f = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro colour
    obtain ⟨p, hp, hL, hR⟩ := hcolouring f colour
    obtain ⟨q, hq⟩ := (folkmanNativeCopySystem.subcopy_range_iff f p).mp ⟨hL, hR⟩
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, by rw [hq, hp]⟩
  rw [hall, Finset.card_univ, Fintype.card_fin] at hf
  exact (Nat.not_le_of_gt t.lt_two_pow_self) hf

/-- No precompact Ramsey expansion exists for the native Folkman–BANANA
copy system, in the shared interface for hereditary expansion types with
the embedding Ramsey property. -/
theorem folkmanNative_noPrecompactRamseyExpansion :
    ¬ Nonempty (RamseyExpansion folkmanNativeCopySystem) := by
  rintro ⟨E⟩
  exact folkmanNativeCopyRamseyDegree_infinite _
    (E.copyRamseyDegreeLE_card_expansionTypes _)

end SuccessorTree.NonPrecompact
