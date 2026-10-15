import BANANA.NonPrecompact.PrebananaFinitePowersetMarkedLifts
import BANANA.NonPrecompact.PrebananaAbstractAtomsLiteral
import BANANA.NonPrecompact.PrebananaAbstractAtomCodes

/-!
# The canonical marked atom-powerset embedding of a finite Boolean algebra

Every finite nontrivial Boolean algebra is the powerset of its atoms.
For a disjoint-additive F₂ marking, the marking on an element equals
the sum of the markings of the atoms below it. Consequently the
canonical finite-atom order isomorphism is not merely a Boolean
isomorphism: it is a genuine marking-preserving embedding into the
concrete marked powerset model used by the five-ary extension proof.

The nonemptiness instance on the abstract atom type is guaranteed
by `prebananaAbstractAtoms_nonempty` and is given explicitly by
callers. This is the target-side representation bridge, not yet the
complete extension square for arbitrary embeddings.
-/

namespace SuccessorTree.NonPrecompact

/-- The canonical finite Boolean-algebra-to-atom-powerset map is a
marked Boolean embedding, with the same F₂ marking on *all* elements. -/
noncomputable def prebananaAbstractModel_markedPowersetEmbedding
    (B : PrebananaFiniteBooleanModel)
    [Nonempty (PrebananaAbstractAtoms B.carrier)] :
    PrebananaFiniteBooleanEmbedding B
      (prebananaFiniteMarkedPowerset
        (PrebananaAbstractAtoms B.carrier)
        (fun a => B.μ (a : B.carrier))
        (prebananaAbstractParity_total_even_on_atoms
          B.carrier B.μ B.μ_bot B.μ_top B.μ_add)) := by
  classical
  let e := prebananaFiniteBooleanAtomFinsetOrderIso B.carrier
  refine {
    hom := {
      toFun := e
      map_bot' := e.map_bot
      map_top' := e.map_top
      map_sup' := by
        intro x y
        exact e.map_sup x y
      map_inf' := by
        intro x y
        exact e.map_inf x y
    }
    injective := e.injective
    preserves_μ := ?_
  }
  intro x
  change (∑ a ∈ e x, B.μ (a : B.carrier)) = B.μ x
  exact (prebananaAbstractParity_atomSum_on_atoms
    B.carrier B.μ B.μ_bot B.μ_add x).symm

end SuccessorTree.NonPrecompact
