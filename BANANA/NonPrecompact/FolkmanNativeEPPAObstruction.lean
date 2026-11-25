import BANANA.NonPrecompact.FolkmanFiniteBooleanEPPA
import BANANA.NonPrecompact.FolkmanNativeModels
import BANANA.NonPrecompact.FolkmanNativeOneAtom

/-!
# Failure of EPPA for Folkman–BANANA

A ring automorphism preserves the set of elements below an element. In
a finite Boolean ring it cannot carry an element to a strict enlargement.
Two non-unital embeddings of the one-atom ring into the two-atom ring,
with both right sorts zero, exhibit the obstruction.
-/

namespace SuccessorTree.NonPrecompact

open FolkmanNativeFiniteModel

/-- EPPA for the native two-sorted finite class. Two embeddings of the
same finite source encode the domain, range and isomorphism between them. -/
def folkmanNativeEPPA : Prop :=
  ∀ A : FolkmanNativeFiniteModel, ∃ (B : FolkmanNativeFiniteModel) (f : Embedding A B),
    ∀ (S : FolkmanNativeFiniteModel) (p q : Embedding S A),
      ∃ e : FolkmanNativeFinitePairingIso B.pairing B.pairing,
        (∀ x, e.left (f.left (p.left x)) = f.left (q.left x)) ∧
        (∀ y, e.right (f.right (p.right y)) = f.right (q.right y))

private noncomputable def zeroRightModel (n : ℕ) : FolkmanNativeFiniteModel where
  Left := FolkmanNativeCodeRing n
  Right := FolkmanNativeCodeRing 0
  pairing := ⟨fun _ _ => 0, fun _ _ _ => by simp, fun _ _ _ => by simp⟩

private noncomputable def embedOneAtom {n : ℕ} (x : FolkmanNativeCodeRing n) (hx : x ≠ 0) :
    Embedding (zeroRightModel 1) (zeroRightModel n) where
  left := folkmanOneAtomHom x
  right := NonUnitalRingHom.id _
  left_injective := folkmanOneAtomHom_injective hx
  right_injective := Function.injective_id
  preserves_pairing _ _ := rfl

/-- The partial isomorphism sending one atom to the whole two-atom left
ring cannot extend to any automorphism of any finite native extension. -/
theorem folkmanNativeEPPA_fails : ¬ folkmanNativeEPPA := by
  classical
  intro h
  let a : FolkmanNativeCodeRing 2 := toBoolRing {0}
  have ha0 : a ≠ 0 := by
    intro ha
    have eq := congrArg ofBoolRing ha
    change ({0} : Finset (Fin 2)) = ∅ at eq
    exact Finset.notMem_empty (0 : Fin 2) (eq ▸ Finset.mem_singleton_self _)
  have h10 : (1 : FolkmanNativeCodeRing 2) ≠ 0 := by
    intro h
    have eq := congrArg ofBoolRing h
    change (Finset.univ : Finset (Fin 2)) = ∅ at eq
    exact Finset.notMem_empty (0 : Fin 2) (eq ▸ Finset.mem_univ _)
  obtain ⟨B, f, hf⟩ := h (zeroRightModel 2)
  obtain ⟨e, he, _⟩ := hf (zeroRightModel 1) (embedOneAtom a ha0) (embedOneAtom 1 h10)
  have he1 := he 1
  change e.left (f.left (folkmanOneAtomHom a 1)) =
    f.left (folkmanOneAtomHom (1 : FolkmanNativeCodeRing 2) 1) at he1
  simp only [folkmanOneAtomHom_one] at he1
  exact folkmanTwoAtom_partialIso_obstructed f.left f.left_injective e.left he1

end SuccessorTree.NonPrecompact
