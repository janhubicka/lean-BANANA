import BANANA.NonPrecompact.FolkmanNativeFiniteIndexMorphisms

/-!
# Native Folkman embeddings become actual atom-code embeddings

The non-unital Boolean-ring code sends each original finite embedding
to a partial owner of target atoms with a nonempty fibre over each
source atom.  The owners on the two sorts, together with the
original pairing-preservation property, form an actual
FolkmanAtomEmbedding, not just two unrelated functions between powersets.

The conversion includes zero rings and permits unused target atoms.
It is the missing morphism-level link between the native class and
the existing countable Fin-indexed atom-presentation class.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff BigOperators


/-- Modulo two the ordinary integer incidence count is the
F₂-bilinear atom-matrix sum. -/
theorem folkmanNativeFin_edgeCount_cast
    (C : FolkmanAtomStructure)
    (X : Finset (Fin C.leftCount))
    (Y : Finset (Fin C.rightCount)) :
    (folkmanEdgeCount C.edge X Y : F2) =
      ∑ i ∈ X, ∑ j ∈ Y, C.edge i j := by
  classical
  have hbit : ∀ z : F2,
      (if z = 1 then (1 : F2) else 0) = z := by
    decide
  simp [folkmanEdgeCount, hbit]

/-- Every pair of injective native non-unital ring homomorphisms
preserving the original two-sort pairing determines a genuine
FolkmanAtomEmbedding between the finite-index object presentations.

This derives the atom owners, their surjective-to-source property,
and the entire F₂ parity pairing condition from the native maps.
Neither source sort is assumed nonzero. -/
theorem folkmanNativeFinCode_exists_atomEmbedding
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
    Nonempty (FolkmanAtomEmbedding
      (folkmanNativeFinCode γA) (folkmanNativeFinCode γB)) := by
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
  }⟩
  · intro i
    obtain ⟨b, hb⟩ := hLnonempty i
    exact ⟨b, by simp [folkmanFiber, hb]⟩
  · intro j
    obtain ⟨b, hb⟩ := hRnonempty j
    exact ⟨b, by simp [folkmanFiber, hb]⟩
  · intro i j
    have hp := folkmanNativeFinRingMaps_preserve_pairing
      fL fR γA γB hAleft hAright hBleft hBright hcompat
      ({i} : Finset (Fin (folkmanNativeFinCode γA).leftCount))
      ({j} : Finset (Fin (folkmanNativeFinCode γA).rightCount))
    rw [hLsingle, hRsingle] at hp
    calc
      (folkmanEdgeCount (folkmanNativeFinCode γB).edge
        (folkmanFiber ownerL i) (folkmanFiber ownerR j) : F2) =
          ∑ x ∈ folkmanFiber ownerL i,
            ∑ y ∈ folkmanFiber ownerR j,
              (folkmanNativeFinCode γB).edge x y :=
        folkmanNativeFin_edgeCount_cast _ _ _
      _ = (folkmanNativeFinCode γA).edge i j := by
        simpa only [Finset.sum_singleton] using hp

end SuccessorTree.NonPrecompact
