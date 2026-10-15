import BANANA.NonPrecompact.PrebananaResidualParity

/-!
# A fibrewise allocation map for finite pre-BANANA extensions

Suppose source atoms α and target atoms β project onto the same
base atom type δ. For each target atom select a distinct source
witness having the same base projection. Also choose one distinguished
target atom over every base atom.

Send selected source witnesses back to their corresponding target
atoms, and all other source leaves to their distinguished target
atom over the same base atom.

This gives a surjective allocation map which commutes *exactly*
with both projections to the base. It is the set-theoretic part
of the finite pre-BANANA extension construction.

Parity preservation requires compatible marking and the residual
parity argument; neither is asserted in this module.
-/

namespace SuccessorTree.NonPrecompact

/-- Witness-retraction allocation, choosing the residual bin
separately for each base atom. -/
noncomputable def prebananaFibrewiseAllocate
    {α β δ : Type*} [Nonempty β]
    (source : α → δ) (witness : β → α)
    (base : δ → β) (x : α) : β := by
  classical
  exact if x ∈ Set.range witness then
    Function.invFun witness x
  else base (source x)

/-- Selected witnesses are mapped back to their target atoms. -/
theorem prebananaFibrewiseAllocate_witness
    {α β δ : Type*} [Nonempty β]
    (source : α → δ) (witness : β → α)
    (hinj : Function.Injective witness)
    (base : δ → β) (b : β) :
    prebananaFibrewiseAllocate source witness base (witness b) = b := by
  classical
  simpa [prebananaFibrewiseAllocate] using
    (Function.leftInverse_invFun hinj b)

/-- Every target atom has a nonempty preimage in the allocation. -/
theorem prebananaFibrewiseAllocate_surjective
    {α β δ : Type*} [Nonempty β]
    (source : α → δ) (witness : β → α)
    (hinj : Function.Injective witness) (base : δ → β) :
    Function.Surjective (prebananaFibrewiseAllocate source witness base) := by
  intro b
  exact ⟨witness b,
    prebananaFibrewiseAllocate_witness source witness hinj base b⟩

/-- A fibrewise allocation respects the base projection on *every*
source leaf, not merely on selected witnesses. -/
theorem prebananaFibrewiseAllocate_commutes
    {α β δ : Type*} [Nonempty β]
    (source : α → δ) (target : β → δ)
    (witness : β → α)
    (hinj : Function.Injective witness)
    (hcompat : ∀ b : β, source (witness b) = target b)
    (base : δ → β)
    (hbase : ∀ a : δ, target (base a) = a)
    (x : α) :
    target (prebananaFibrewiseAllocate source witness base x) =
      source x := by
  classical
  by_cases hx : x ∈ Set.range witness
  · obtain ⟨b, rfl⟩ := hx
    rw [prebananaFibrewiseAllocate_witness source witness hinj base b]
    exact (hcompat b).symm
  · simp [prebananaFibrewiseAllocate, hx, hbase]

end SuccessorTree.NonPrecompact
