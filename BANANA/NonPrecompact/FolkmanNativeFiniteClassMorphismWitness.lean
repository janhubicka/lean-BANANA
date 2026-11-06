import BANANA.NonPrecompact.FolkmanNativeFiniteCodeEmbedding

/-!
# Track B: faithful atom owners for a native Folkman embedding

The earlier existence theorem produces a finite atom embedding, but its
conclusion alone does not connect the chosen atom owners to the *given*
native ring homomorphisms.  This stronger existential certificate records
those equations on EVERY source ring element, making the morphism
conversion usable in later class-level and limit arguments.

No assumption of a multiplicative unit, nonzero sort or preservation of
the greatest element occurs here.  This proof is UNVERIFIED until a
pinned local Lean build and axiom audit.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff BigOperators


/-- Every native two-sort embedding has a finite-code representation
whose actual owner fibres reproduce BOTH original ring maps on all
finite supports, and whose cross-pairing is exactly preserved. -/
theorem folkmanNativeFinCode_exists_atomEmbedding_with_maps
    {AL AR BL BR : Type*}
    [BooleanRing AL] [Fintype AL]
    [BooleanRing AR] [Fintype AR]
    [BooleanRing BL] [Fintype BL]
    [BooleanRing BR] [Fintype BR]
    (fL : AL →ₙ+* BL) (fR : AR →ₙ+* BR)
    (hfL : Function.Injective fL)
    (hfR : Function.Injective fR)
    (γA : AL → AR → F2) (γB : BL → BR → F2)
    (hAleft : ∀ x x' y, γA (x + x') y = γA x y + γA x' y)
    (hAright : ∀ x y y', γA x (y + y') = γA x y + γA x y')
    (hBleft : ∀ x x' y, γB (x + x') y = γB x y + γB x' y)
    (hBright : ∀ x y y', γB x (y + y') = γB x y + γB x y')
    (hcompat : ∀ x y, γB (fL x) (fR y) = γA x y) :
    ∃ E : FolkmanAtomEmbedding
        (folkmanNativeFinCode γA) (folkmanNativeFinCode γB),
      (∀ s, folkmanNativeFinRingMap fL s =
        s.biUnion (folkmanFiber E.leftOwner)) ∧
      (∀ t, folkmanNativeFinRingMap fR t =
        t.biUnion (folkmanFiber E.rightOwner)) := by
  classical
  obtain ⟨ownerL, hLnonempty, hLmap⟩ :=
    folkmanNativeFinRingMap_exists_partialOwner fL hfL
  obtain ⟨ownerR, hRnonempty, hRmap⟩ :=
    folkmanNativeFinRingMap_exists_partialOwner fR hfR
  have hLsingle :
      ∀ i, folkmanNativeFinRingMap fL {i} =
        folkmanFiber ownerL i := by
    intro i
    rw [hLmap]
    ext b
    simp [folkmanFiber]
  have hRsingle :
      ∀ j, folkmanNativeFinRingMap fR {j} =
        folkmanFiber ownerR j := by
    intro j
    rw [hRmap]
    ext b
    simp [folkmanFiber]
  refine ⟨{
    leftOwner := ownerL
    rightOwner := ownerR
    left_fibre_nonempty := ?_
    right_fibre_nonempty := ?_
    pairing_parity := ?_
  }, ?_, ?_⟩
  · intro i
    obtain ⟨b, hb⟩ := hLnonempty i
    refine ⟨b, ?_⟩
    simpa only [folkmanFiber, Finset.mem_filter, Finset.mem_univ,
      true_and, Set.mem_setOf_eq] using hb
  · intro j
    obtain ⟨b, hb⟩ := hRnonempty j
    refine ⟨b, ?_⟩
    simpa only [folkmanFiber, Finset.mem_filter, Finset.mem_univ,
      true_and, Set.mem_setOf_eq] using hb
  · intro i j
    have hp := folkmanNativeFinRingMaps_preserve_pairing
      fL fR γA γB hAleft hAright hBleft hBright hcompat
      ({i} : Finset (Fin (folkmanNativeFinCode γA).leftCount))
      ({j} : Finset (Fin (folkmanNativeFinCode γA).rightCount))
    have hp' :
        (∑ x ∈ folkmanNativeFinRingMap fL ({i} : Finset _),
          ∑ y ∈ folkmanNativeFinRingMap fR ({j} : Finset _),
            (folkmanNativeFinCode γB).edge x y) =
          (folkmanNativeFinCode γA).edge i j := by
      refine hp.trans ?_
      simp
    have hsum :
        (∑ x ∈ folkmanFiber ownerL i,
          ∑ y ∈ folkmanFiber ownerR j,
            (folkmanNativeFinCode γB).edge x y) =
        ∑ x ∈ folkmanNativeFinRingMap fL ({i} : Finset _),
          ∑ y ∈ folkmanNativeFinRingMap fR ({j} : Finset _),
            (folkmanNativeFinCode γB).edge x y := by
      apply Finset.sum_congr (hLsingle i).symm
      intro x hx
      apply Finset.sum_congr (hRsingle j).symm
      intro y hy
      rfl
    calc
      (folkmanEdgeCount (folkmanNativeFinCode γB).edge
        (folkmanFiber ownerL i) (folkmanFiber ownerR j) : F2) =
          ∑ x ∈ folkmanFiber ownerL i,
            ∑ y ∈ folkmanFiber ownerR j,
              (folkmanNativeFinCode γB).edge x y :=
        folkmanNativeFin_edgeCount_cast _ _ _
      _ = ∑ x ∈ folkmanNativeFinRingMap fL ({i} : Finset _),
          ∑ y ∈ folkmanNativeFinRingMap fR ({j} : Finset _),
            (folkmanNativeFinCode γB).edge x y := hsum
      _ = (folkmanNativeFinCode γA).edge i j := hp'
  · intro s
    rw [hLmap]
    ext b
    simp [folkmanFiber]
  · intro t
    rw [hRmap]
    ext b
    simp [folkmanFiber]

end SuccessorTree.NonPrecompact
