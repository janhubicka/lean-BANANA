import BANANA.NonPrecompact.PrebananaResidualParity

/-!
# Assigning unselected atoms to one distinguished target bin

Suppose each target atom b has already been assigned a *different*
source leaf by an injective witness map. Send every witness leaf
back to its target atom, and send every other leaf to one chosen
target atom b₀.

This produces a surjective atom-partition map. Every target atom
other than b₀ receives only its designated witness; only b₀
receives the residual leaves. The preceding residual-parity lemmas
show why such a map preserves target marks once the witnesses
have the required marks and total parity.

The construction here is entirely set-theoretic. Selection of
mark-compatible witnesses and the final parity statement are not
claimed.
-/

namespace SuccessorTree.NonPrecompact

/-- Use the inverse of a witness injection on its image, and assign
all unselected source leaves to one distinguished target atom. -/
noncomputable def prebananaAllocateWitnesses
    {α β : Type*} (witness : β → α) (base : β) (x : α) : β := by
  classical
  letI : Nonempty β := ⟨base⟩
  exact if x ∈ Set.range witness then Function.invFun witness x else base

/-- The allocation sends every designated witness to its own bin. -/
theorem prebananaAllocateWitnesses_witness
    {α β : Type*} (witness : β → α)
    (hinj : Function.Injective witness) (base : β) (b : β) :
    prebananaAllocateWitnesses witness base (witness b) = b := by
  classical
  letI : Nonempty β := ⟨base⟩
  simp [prebananaAllocateWitnesses, Function.leftInverse_invFun hinj]

/-- Every target atom has a nonempty fibre, witnessed by its
selected source leaf. -/
theorem prebananaAllocateWitnesses_surjective
    {α β : Type*} (witness : β → α)
    (hinj : Function.Injective witness) (base : β) :
    Function.Surjective (prebananaAllocateWitnesses witness base) := by
  intro b
  exact ⟨witness b, prebananaAllocateWitnesses_witness witness hinj base b⟩

/-- All unselected leaves are assigned to the distinguished bin. -/
theorem prebananaAllocateWitnesses_unselected
    {α β : Type*} (witness : β → α) (base : β)
    {x : α} (hx : x ∉ Set.range witness) :
    prebananaAllocateWitnesses witness base x = base := by
  classical
  simp [prebananaAllocateWitnesses, hx]

/-- For every other target atom, its unique preimage is its
designated witness. -/
theorem prebananaAllocateWitnesses_nonbase
    {α β : Type*} (witness : β → α)
    (hinj : Function.Injective witness)
    (base b : β) (hb : b ≠ base)
    (x : α)
    (hx : prebananaAllocateWitnesses witness base x = b) :
    x = witness b := by
  classical
  by_cases hrange : x ∈ Set.range witness
  · obtain ⟨a, rfl⟩ := hrange
    rw [prebananaAllocateWitnesses_witness witness hinj base a] at hx
    rw [← hx]
  · rw [prebananaAllocateWitnesses_unselected witness base hrange] at hx
    exact False.elim (hb hx.symm)

end SuccessorTree.NonPrecompact
