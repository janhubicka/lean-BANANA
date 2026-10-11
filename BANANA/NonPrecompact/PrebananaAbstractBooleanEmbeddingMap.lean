import BANANA.NonPrecompact.PrebananaFiniteBooleanRepresentation

/-!
# Conjugating arbitrary finite Boolean embeddings to atom powersets

Every finite Boolean algebra is canonically an atom powerset, as
formalised in `PrebananaFiniteBooleanRepresentation`. A map
preserving bottom, top, joins, and meets becomes a map of finite
atom subsets preserving empty, full, union, and intersection.
Injectivity is also preserved. No marking assumptions are
needed for this Boolean-algebraic step.

This is the abstract side of the converse atom-partition theorem.
-/

namespace SuccessorTree.NonPrecompact

/-- Conjugate a map of finite Boolean algebras by their canonical
order isomorphisms to finite powersets of atoms. -/
noncomputable def prebananaAbstractPowersetMap
    {α β : Type*}
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (φ : α → β) :
    Finset (PrebananaAbstractAtoms α) →
      Finset (PrebananaAbstractAtoms β) :=
  fun s =>
    (prebananaFiniteBooleanAtomFinsetOrderIso β)
      (φ ((prebananaFiniteBooleanAtomFinsetOrderIso α).symm s))

theorem prebananaAbstractPowersetMap_empty
    {α β : Type*}
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (φ : α → β) (hbot : φ ⊥ = ⊥) :
    prebananaAbstractPowersetMap φ ∅ = ∅ := by
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso α
  let eB := prebananaFiniteBooleanAtomFinsetOrderIso β
  change eB (φ (eA.symm (∅ : Finset (PrebananaAbstractAtoms α)))) = ∅
  rw [show eA.symm (∅ : Finset (PrebananaAbstractAtoms α)) = (⊥ : α)
    from eA.symm.map_bot, hbot]
  exact eB.map_bot

theorem prebananaAbstractPowersetMap_univ
    {α β : Type*}
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (φ : α → β) (htop : φ ⊤ = ⊤) :
    prebananaAbstractPowersetMap φ Finset.univ = Finset.univ := by
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso α
  let eB := prebananaFiniteBooleanAtomFinsetOrderIso β
  change eB (φ (eA.symm (Finset.univ :
    Finset (PrebananaAbstractAtoms α)))) = Finset.univ
  rw [show eA.symm (Finset.univ : Finset (PrebananaAbstractAtoms α)) =
      (⊤ : α) from eA.symm.map_top, htop]
  exact eB.map_top

theorem prebananaAbstractPowersetMap_union
    {α β : Type*}
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (φ : α → β)
    (hsup : ∀ x y : α, φ (x ⊔ y) = φ x ⊔ φ y)
    (s t : Finset (PrebananaAbstractAtoms α)) :
    prebananaAbstractPowersetMap φ (s ∪ t) =
      prebananaAbstractPowersetMap φ s ∪
      prebananaAbstractPowersetMap φ t := by
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso α
  let eB := prebananaFiniteBooleanAtomFinsetOrderIso β
  change eB (φ (eA.symm (s ⊔ t))) =
    eB (φ (eA.symm s)) ⊔ eB (φ (eA.symm t))
  rw [eA.symm.map_sup, hsup, eB.map_sup]

theorem prebananaAbstractPowersetMap_inter
    {α β : Type*}
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (φ : α → β)
    (hinf : ∀ x y : α, φ (x ⊓ y) = φ x ⊓ φ y)
    (s t : Finset (PrebananaAbstractAtoms α)) :
    prebananaAbstractPowersetMap φ (s ∩ t) =
      prebananaAbstractPowersetMap φ s ∩
      prebananaAbstractPowersetMap φ t := by
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso α
  let eB := prebananaFiniteBooleanAtomFinsetOrderIso β
  change eB (φ (eA.symm (s ⊓ t))) =
    eB (φ (eA.symm s)) ⊓ eB (φ (eA.symm t))
  rw [eA.symm.map_inf, hinf, eB.map_inf]

theorem prebananaAbstractPowersetMap_injective
    {α β : Type*}
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (φ : α → β) (hinj : Function.Injective φ) :
    Function.Injective (prebananaAbstractPowersetMap φ) := by
  intro s t h
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso α
  let eB := prebananaFiniteBooleanAtomFinsetOrderIso β
  change eB (φ (eA.symm s)) = eB (φ (eA.symm t)) at h
  exact eA.symm.injective (hinj (eB.injective h))

end SuccessorTree.NonPrecompact
