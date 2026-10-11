import BANANA.NonPrecompact.PrebananaPowersetBridge

/-!
# Marked Boolean embeddings induced from faithful atom codes

The finite pre-BANANA powerset map is already a genuine Boolean
embedding preserving the additive F₂ marking. Any injective,
Boolean-operation-preserving code of an abstract finite Boolean
algebra gives a marked Boolean embedding into a powerset amalgam by
composition with that map.

This lemma isolates the operation and marking requirements that
remain after the independent strong-intersection diagram chase.
It is conditional on the code properties; the abstract Boolean
element-code modules supply them separately.
-/

namespace SuccessorTree.NonPrecompact

/-- Composition with a genuine marked atom embedding preserves
injectivity, bottom, top, joins, meets and the parity marking of
any faithful Boolean element code. -/
theorem prebananaCodedBooleanEmbedding_properties
    {β : Type*} [BooleanAlgebra β]
    (B D : PrebananaAtomStructure)
    (u : PrebananaAtomEmbedding B D)
    (codeB : β → Finset (Fin B.atomCount))
    (μB : β → F2)
    (hinj : Function.Injective codeB)
    (hbot : codeB ⊥ = ∅)
    (htop : codeB ⊤ = Finset.univ)
    (hsup : ∀ x y : β, codeB (x ⊔ y) = codeB x ∪ codeB y)
    (hinf : ∀ x y : β, codeB (x ⊓ y) = codeB x ∩ codeB y)
    (hmark : ∀ x : β,
      prebananaBooleanParity B (codeB x) = μB x) :
    ∃ h : β → Finset (Fin D.atomCount),
      (∀ x : β, h x = prebananaBooleanMap u (codeB x)) ∧
      Function.Injective h ∧
      h ⊥ = ∅ ∧
      h ⊤ = Finset.univ ∧
      (∀ x y : β, h (x ⊔ y) = h x ∪ h y) ∧
      (∀ x y : β, h (x ⊓ y) = h x ∩ h y) ∧
      (∀ x : β, prebananaBooleanParity D (h x) = μB x) := by
  classical
  let h : β → Finset (Fin D.atomCount) :=
    fun x => prebananaBooleanMap u (codeB x)
  refine ⟨h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x y hxy
    exact hinj ((prebananaBooleanMap_injective u) hxy)
  · change prebananaBooleanMap u (codeB (⊥ : β)) = ∅
    rw [hbot, prebananaBooleanMap_empty]
  · change prebananaBooleanMap u (codeB (⊤ : β)) = Finset.univ
    rw [htop, prebananaBooleanMap_univ]
  · intro x y
    change prebananaBooleanMap u (codeB (x ⊔ y)) =
      prebananaBooleanMap u (codeB x) ∪ prebananaBooleanMap u (codeB y)
    rw [hsup, prebananaBooleanMap_union]
  · intro x y
    change prebananaBooleanMap u (codeB (x ⊓ y)) =
      prebananaBooleanMap u (codeB x) ∩ prebananaBooleanMap u (codeB y)
    rw [hinf, prebananaBooleanMap_inter]
  · intro x
    change prebananaBooleanParity D (prebananaBooleanMap u (codeB x)) = μB x
    exact (prebananaBooleanMap_parity u (codeB x)).trans (hmark x)

end SuccessorTree.NonPrecompact
