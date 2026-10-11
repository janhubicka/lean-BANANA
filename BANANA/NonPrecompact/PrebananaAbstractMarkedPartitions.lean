import BANANA.NonPrecompact.PrebananaPowersetMapPartitions
import BANANA.NonPrecompact.PrebananaAbstractBooleanEmbeddingMap
import BANANA.NonPrecompact.PrebananaAbstractParityDecomposition

/-!
# The atom partition of an arbitrary finite Boolean embedding

The canonical finite atom-powerset order isomorphism transports
any injective bottom/top/join/meet-preserving map of finite Boolean
algebras to an injective Boolean map of finite atom subsets.
The powerset reconstruction theorem supplies a surjection from
target atoms onto source atoms. Preservation of the additive F₂
marking then gives the prescribed parity on each source atom fibre.

This statement uses singleton *representatives* of abstract atoms;
the separate literal-singleton lemma identifies those with the
actual elements of the original Boolean algebras.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- An arbitrary embedding of finite Boolean algebras is inverse
image along a surjection of their abstract atom sets. -/
theorem prebananaAbstractEmbedding_exists_atomPartition
    (α β : Type*)
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (φ : α → β)
    (hinj : Function.Injective φ)
    (hbot : φ ⊥ = ⊥)
    (htop : φ ⊤ = ⊤)
    (hsup : ∀ x y : α, φ (x ⊔ y) = φ x ⊔ φ y)
    (hinf : ∀ x y : α, φ (x ⊓ y) = φ x ⊓ φ y) :
    ∃ part : PrebananaAbstractAtoms β → PrebananaAbstractAtoms α,
      Function.Surjective part ∧
      ∀ s : Finset (PrebananaAbstractAtoms α),
        prebananaAbstractPowersetMap φ s =
          Finset.univ.filter (fun b => part b ∈ s) := by
  classical
  exact prebanana_exists_atomPartition_of_powersetEmbedding
    (prebananaAbstractPowersetMap φ)
    (prebananaAbstractPowersetMap_empty φ hbot)
    (prebananaAbstractPowersetMap_univ φ htop)
    (prebananaAbstractPowersetMap_union φ hsup)
    (prebananaAbstractPowersetMap_inter φ hinf)
    (prebananaAbstractPowersetMap_injective φ hinj)

/-- If the abstract embedding also preserves an additive parity
function, its atom-fibre partition has the required F₂ totals.
The terms in the sum are the singleton atom representatives from
the canonical finite powerset representation. -/
theorem prebananaAbstractEmbedding_exists_markedAtomPartition
    (α β : Type*)
    [BooleanAlgebra α] [Fintype α]
    [BooleanAlgebra β] [Fintype β]
    (μA : α → F2) (μB : β → F2)
    (hzeroB : μB ⊥ = 0)
    (haddB : ∀ x y : β, x ⊓ y = ⊥ →
      μB (x ⊔ y) = μB x + μB y)
    (φ : α → β)
    (hinj : Function.Injective φ)
    (hbot : φ ⊥ = ⊥)
    (htop : φ ⊤ = ⊤)
    (hsup : ∀ x y : α, φ (x ⊔ y) = φ x ⊔ φ y)
    (hinf : ∀ x y : α, φ (x ⊓ y) = φ x ⊓ φ y)
    (hmark : ∀ x : α, μB (φ x) = μA x) :
    ∃ part : PrebananaAbstractAtoms β → PrebananaAbstractAtoms α,
      Function.Surjective part ∧
      (∀ s : Finset (PrebananaAbstractAtoms α),
        prebananaAbstractPowersetMap φ s =
          Finset.univ.filter (fun b => part b ∈ s)) ∧
      (∀ a : PrebananaAbstractAtoms α,
        (∑ b ∈ (Finset.univ : Finset (PrebananaAbstractAtoms β)).filter
          (fun b => part b = a),
            μB ((prebananaFiniteBooleanAtomFinsetOrderIso β).symm
              ({b} : Finset (PrebananaAbstractAtoms β)))) =
        μA ((prebananaFiniteBooleanAtomFinsetOrderIso α).symm
          ({a} : Finset (PrebananaAbstractAtoms α)))) := by
  classical
  obtain ⟨part, hsurj, hpart⟩ :=
    prebananaAbstractEmbedding_exists_atomPartition α β
      φ hinj hbot htop hsup hinf
  refine ⟨part, hsurj, hpart, ?_⟩
  intro a
  let eA := prebananaFiniteBooleanAtomFinsetOrderIso α
  let eB := prebananaFiniteBooleanAtomFinsetOrderIso β
  let F : Finset (PrebananaAbstractAtoms α) →
      Finset (PrebananaAbstractAtoms β) :=
    prebananaAbstractPowersetMap φ
  have hF : F {a} =
      (Finset.univ : Finset (PrebananaAbstractAtoms β)).filter
        (fun b => part b = a) := by
    simpa only [Finset.mem_singleton] using
      hpart ({a} : Finset (PrebananaAbstractAtoms α))
  have hsum :
      μB (φ (eA.symm ({a} : Finset (PrebananaAbstractAtoms α)))) =
      ∑ b ∈ F {a},
        μB (eB.symm ({b} : Finset (PrebananaAbstractAtoms β))) := by
    simpa [F, prebananaAbstractPowersetMap, eA, eB] using
      (prebananaAbstractParity_atomSum β μB hzeroB haddB
        (φ (eA.symm ({a} : Finset (PrebananaAbstractAtoms α)))))
  change
    (∑ b ∈ (Finset.univ : Finset (PrebananaAbstractAtoms β)).filter
      (fun b => part b = a),
        μB (eB.symm ({b} : Finset (PrebananaAbstractAtoms β)))) =
    μA (eA.symm ({a} : Finset (PrebananaAbstractAtoms α)))
  calc
    (∑ b ∈ (Finset.univ : Finset (PrebananaAbstractAtoms β)).filter
      (fun b => part b = a),
        μB (eB.symm ({b} : Finset (PrebananaAbstractAtoms β)))) =
      ∑ b ∈ F {a},
        μB (eB.symm ({b} : Finset (PrebananaAbstractAtoms β))) := by
        rw [hF]
    _ = μB (φ (eA.symm ({a} : Finset (PrebananaAbstractAtoms α)))) :=
      hsum.symm
    _ = μA (eA.symm ({a} : Finset (PrebananaAbstractAtoms α))) :=
      hmark _

end SuccessorTree.NonPrecompact
