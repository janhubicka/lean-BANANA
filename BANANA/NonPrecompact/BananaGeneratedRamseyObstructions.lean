import BANANA.NonPrecompact.BananaFunctionalCopyDegree
import BANANA.NonPrecompact.BooleanBananaFirstOrderRamseyObstruction
import BANANA.NonPrecompact.FirstOrderGeneratedRamseyExpansion
import BANANA.NonPrecompact.FolkmanFirstOrderRamseyObstruction

/-!
# Generated expansion obstructions for the three BANANA classes

The established infinite copy degrees rule out hereditary Ramsey expansions
whose pointed generated expansion types are finite in number.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder

namespace BooleanBanana

/-- The marked Boolean age has no precompact Ramsey expansion when expansion
types record the generated expanded substructure and its distinguished copy. -/
theorem cylinder_noPrecompactGeneratedRamseyExpansion :
    ¬ FirstOrderRamseyExpansion.HasPrecompactGeneratedRamseyExpansion
      (markedBooleanLanguage.age PrebananaFiveAryCylinderLimitCarrier) :=
  FirstOrderRamseyExpansion.not_hasPrecompactGeneratedRamseyExpansion
    cylinder_age_finite cylinderTwoMarkedAgeObject cylinderTwoMarkedCopyRamseyDegree_infinite

end BooleanBanana

namespace FolkmanFirstOrder

/-- The encoded Folkman class has no precompact Ramsey expansion when
expansion types count pointed generated substructures. -/
theorem not_hasPrecompactGeneratedRamseyExpansion :
    ¬ FirstOrderRamseyExpansion.HasPrecompactGeneratedRamseyExpansion folkmanFirstOrderClass :=
  FirstOrderRamseyExpansion.not_hasPrecompactGeneratedRamseyExpansion
    finite_of_mem (diagonal 1) copyRamseyDegree_infinite

end FolkmanFirstOrder

namespace BananaFunctional

/-- The functional BANANA age has no precompact Ramsey expansion when
expansion types count pointed generated substructures. -/
theorem functionalAge_noPrecompactGeneratedRamseyExpansion :
    ¬ FirstOrderRamseyExpansion.HasPrecompactGeneratedRamseyExpansion functionalAge :=
  FirstOrderRamseyExpansion.not_hasPrecompactGeneratedRamseyExpansion
    finite_of_mem_functionalAge (matrixAgeObject ⟨1, 1, linePairSource 0⟩)
      linePair_infinite_copyRamseyDegree

end BananaFunctional

end SuccessorTree.NonPrecompact
