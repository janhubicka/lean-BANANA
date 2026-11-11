import BANANA.NonPrecompact.FolkmanFinitePairedBridgeSwap

/-!
Track C source-only exact-statement audit: swapping the two faithful
copies of a finite paired Folkman bridge makes its source-right/left
extension properties imply its target-right/left properties.

Neither the finite original pairing nor any ambient unit is changed.
The printed transitive axioms require an exact-head local Lean build.
-/

#print axioms SuccessorTree.NonPrecompact.FolkmanFinitePairedBridge.swap
#print axioms SuccessorTree.NonPrecompact.FolkmanFinitePairedBridge.swap_swap
#print axioms SuccessorTree.NonPrecompact.FolkmanFinitePairedBridgeMap.swap
#print axioms SuccessorTree.NonPrecompact.folkmanFinitePairedBridge_swap_monotone
#print axioms SuccessorTree.NonPrecompact.FolkmanFinitePairedBridgeForthExtension
#print axioms SuccessorTree.NonPrecompact.FolkmanFinitePairedBridgeForthExtension.targetLeft
#print axioms SuccessorTree.NonPrecompact.FolkmanFinitePairedBridgeForthExtension.targetRight
#print axioms SuccessorTree.NonPrecompact.FolkmanFinitePairedBridgeForthExtension.toOnePointExtension
