import BANANA.NonPrecompact.FolkmanRingPartialOwners
import Mathlib.Algebra.Ring.BooleanRing

/-!
# The actual native non-unital Boolean-ring embedding interface

The Folkman language has zero, symmetric difference (ring addition)
and intersection (ring multiplication), but does *not* require an
embedding to preserve the ring unit.  Mathlib's RingHom.asBoolAlg is
therefore unsuitable: it is a bounded lattice homomorphism.

We use NonUnitalRingHom, convert each finite Boolean ring to the
corresponding Boolean algebra via AsBoolAlg, and recover the
Option-valued atom-owner map without requiring preservation of top.

Mathlib's BooleanRing identities x ⊔ y = x + y + x*y and
x ⊓ y = x*y give the needed joins and meets.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Transfer the finite atom carrier through Mathlib's Boolean-ring
    type synonym. The resulting finite type is used only locally. -/
local instance folkmanAsBoolAlgFintype (γ : Type*) [Fintype γ] :
    Fintype (AsBoolAlg γ) := Fintype.ofEquiv γ toBoolAlg

/-- A non-unital Boolean-ring homomorphism becomes a bottom-, join-,
and meet-preserving map between the associated Boolean algebras.
This does not assert preservation of top. -/
theorem folkmanNonUnitalRingHom_asBoolAlg_operations
    {α β : Type*} [BooleanRing α] [BooleanRing β]
    (f : α →ₙ+* β) :
    let φ : AsBoolAlg α → AsBoolAlg β :=
      fun x => toBoolAlg (f (ofBoolAlg x))
    φ ⊥ = ⊥ ∧
      (∀ x y, φ (x ⊔ y) = φ x ⊔ φ y) ∧
      (∀ x y, φ (x ⊓ y) = φ x ⊓ φ y) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · simp
  · intro x y
    change toBoolAlg (f (ofBoolAlg (x ⊔ y))) =
      toBoolAlg (f (ofBoolAlg x)) ⊔ toBoolAlg (f (ofBoolAlg y))
    simp only [ofBoolAlg_sup, map_add, map_mul, toBoolAlg_add_add_mul]
  · intro x y
    change toBoolAlg (f (ofBoolAlg (x ⊓ y))) =
      toBoolAlg (f (ofBoolAlg x)) ⊓ toBoolAlg (f (ofBoolAlg y))
    simp only [ofBoolAlg_inf, map_mul, toBoolAlg_mul]

/-- The transported non-unital Boolean-ring embedding is injective
whenever the original ring map is injective. -/
theorem folkmanNonUnitalRingHom_asBoolAlg_injective
    {α β : Type*} [BooleanRing α] [BooleanRing β]
    (f : α →ₙ+* β) (hinj : Function.Injective f) :
    Function.Injective
      (fun x : AsBoolAlg α => toBoolAlg (f (ofBoolAlg x))) := by
  intro x y hxy
  have hf : f (ofBoolAlg x) = f (ofBoolAlg y) :=
    (toBoolAlg_inj).mp hxy
  exact (ofBoolAlg_inj).mp (hinj hf)

/-- Every native injective *non-unital* Boolean-ring homomorphism
between finite Boolean rings is represented by a partial owner of
target atoms, with nonempty fibres over every source atom.

No top-preservation assumption is present.  This includes the
one-element zero ring, whose atom set is empty. -/
theorem folkmanNonUnitalRingEmbedding_exists_partialAtomOwner
    {α β : Type*}
    [BooleanRing α] [Fintype α]
    [BooleanRing β] [Fintype β]
    (f : α →ₙ+* β)
    (hinj : Function.Injective f) :
    ∃ part :
        PrebananaAbstractAtoms (AsBoolAlg β) →
          Option (PrebananaAbstractAtoms (AsBoolAlg α)),
      (∀ a : PrebananaAbstractAtoms (AsBoolAlg α),
        ∃ b : PrebananaAbstractAtoms (AsBoolAlg β),
          part b = some a) ∧
      (∀ s : Finset (PrebananaAbstractAtoms (AsBoolAlg α)),
        prebananaAbstractPowersetMap
            (fun x : AsBoolAlg α => toBoolAlg (f (ofBoolAlg x))) s =
          Finset.univ.filter (fun b => ∃ a ∈ s, part b = some a)) := by
  classical
  let φ : AsBoolAlg α → AsBoolAlg β :=
    fun x => toBoolAlg (f (ofBoolAlg x))
  obtain ⟨hzero, hsup, hinf⟩ :=
    folkmanNonUnitalRingHom_asBoolAlg_operations f
  exact folkmanAbstractEmbedding_exists_partialAtomOwner
    (AsBoolAlg α) (AsBoolAlg β) φ
    (folkmanNonUnitalRingHom_asBoolAlg_injective f hinj)
    hzero hsup hinf

end SuccessorTree.NonPrecompact
