import BANANA.NonPrecompact.FolkmanFiniteTwoSortRingDiagram

/-!
# Transporting exact strong intersection through coordinate equivalences

The finite-atom amalgam has exact common-base intersection.  This
lemma transports that statement from atom subsets to arbitrary source
carriers represented by equivalences, provided the base maps commute
with those equivalences.

No linearity or ring-unit assumption is needed: these belong to the
specific canonical representations used by applications.  In
particular, this works for zero-ring carriers and for non-unital
Boolean-ring embeddings.
-/

namespace SuccessorTree.NonPrecompact
namespace FolkmanFiniteTwoSortAtomDiagram

variable {AL BL CL AR BR CR : Type*}
variable [Fintype AL] [Fintype BL] [Fintype CL]
variable [Fintype AR] [Fintype BR] [Fintype CR]

/-- Exact common-base intersection is invariant under faithful
coordinate equivalences on the three two-sorted carrier pairs. -/
theorem images_eq_iff_common_base_of_equivs
    (D : FolkmanFiniteTwoSortAtomDiagram AL BL CL AR BR CR)
    {A B C : Type*}
    (eA : A ≃ Finset AL × Finset AR)
    (eB : B ≃ Finset BL × Finset BR)
    (eC : C ≃ Finset CL × Finset CR)
    (f : A → B) (g : A → C)
    (hf : ∀ a, D.baseB (eA a) = eB (f a))
    (hg : ∀ a, D.baseC (eA a) = eC (g a))
    (b : B) (c : C) :
    D.embedB (eB b) = D.embedC (eC c) ↔
      ∃ a : A, b = f a ∧ c = g a := by
  classical
  constructor
  · intro h
    obtain ⟨s, hb, hc⟩ :=
      (D.images_eq_iff_common_base (eB b) (eC c)).mp h
    refine ⟨eA.symm s, ?_, ?_⟩
    · apply eB.injective
      calc
        eB b = D.baseB s := hb
        _ = D.baseB (eA (eA.symm s)) := by simp
        _ = eB (f (eA.symm s)) := hf _
    · apply eC.injective
      calc
        eC c = D.baseC s := hc
        _ = D.baseC (eA (eA.symm s)) := by simp
        _ = eC (g (eA.symm s)) := hg _
  · rintro ⟨a, rfl, rfl⟩
    rw [← hf a, ← hg a]
    exact D.base_commutes (eA a)

end FolkmanFiniteTwoSortAtomDiagram
end SuccessorTree.NonPrecompact
