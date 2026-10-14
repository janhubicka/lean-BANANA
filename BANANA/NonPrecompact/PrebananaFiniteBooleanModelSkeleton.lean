import BANANA.NonPrecompact.PrebananaFiniteBooleanModelJEP
import BANANA.NonPrecompact.PrebananaCanonicalFaithfulCodes

/-!
# Countable skeleton of finite marked Boolean models

Every actual finite marked Boolean algebra admits a surjective
marking-preserving bounded-lattice embedding into the canonical finite
atom powerset coded by a PrebananaAtomStructure.

Together with the existing Countable PrebananaAtomStructure instance,
this shows that there are only countably many finite pre-BANANA
isomorphism types. It avoids the false claim that the collection of
all possible finite carrier types itself is countable.
-/

namespace SuccessorTree.NonPrecompact

/-- Every finite marked Boolean model is isomorphic, through an
actual marked Boolean embedding, to its canonical atom-coded model.
The embedding is both injective (by definition) and surjective. -/
theorem prebananaFiniteBooleanModel_hasCanonicalAtomPresentation
    (A : PrebananaFiniteBooleanModel) :
    ∃ D : PrebananaAtomStructure,
      ∃ f : PrebananaFiniteBooleanEmbedding A
        (prebananaAtomFiniteBooleanModel D),
        Function.Surjective f.hom := by
  classical
  let D :=
    prebananaAbstractAtomCode A.carrier A.μ
      A.μ_bot A.μ_top A.μ_add
  let code :=
    prebananaCanonicalFaithfulFiniteCode A.carrier A.μ
      A.μ_bot A.μ_top A.μ_add
  let h : PrebananaMarkedFiniteMap A.carrier D A.μ := {
    toFun := code.toFun
    injective := code.injective
    map_bot := code.map_bot
    map_top := code.map_top
    map_sup := code.map_sup
    map_inf := code.map_inf
    map_parity := code.map_parity
  }
  refine ⟨D, h.toFiniteBooleanEmbedding, ?_⟩
  exact code.surjective

end SuccessorTree.NonPrecompact
