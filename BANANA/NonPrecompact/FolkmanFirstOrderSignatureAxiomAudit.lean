import BANANA.NonPrecompact.FolkmanFirstOrderSignature

/-!
Track C first-order signature audit. This only establishes the
finite original-language symbol inventory and its countability.
No first-order structure encoding, Fraïssé limit or
global automorphism theorem is asserted by these declarations.

The displayed transitive axiom queries must be executed by an
exact-head pinned Lean kernel build; they have not run here.
-/

#print axioms SuccessorTree.NonPrecompact.folkmanFirstOrderFunctions
#print axioms SuccessorTree.NonPrecompact.folkmanFirstOrderRelations
#print axioms SuccessorTree.NonPrecompact.folkmanFirstOrderFunctionsFintype
#print axioms SuccessorTree.NonPrecompact.folkmanFirstOrderRelationsFintype
#print axioms SuccessorTree.NonPrecompact.folkmanFirstOrderLanguage
#print axioms SuccessorTree.NonPrecompact.folkmanFirstOrderFunctionSymbolsCountable
