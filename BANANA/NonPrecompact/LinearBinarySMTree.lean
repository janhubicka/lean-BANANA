import BANANA.NonPrecompact.LinearBinaryM2
import BANANA.NonPrecompact.LinearBinaryDuplication

/-!
# The linear binary successor-tree instance

This packages the binary prefix tree together with the monoid of shape maps
which are linear on every level.  M1 is closure of levelwise linearity, M2 is
skipped-coordinate contraction followed by linear reinsertion, and M3 is the
coordinate-projection duplication map.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

/-- The successor-tree instance whose finite exact approximations encode
binary vector subspaces in row-echelon coordinates. -/
def linearBinarySMTree : SMTree binarySucc where
  M := {F | LinearOnLevels F}
  id_mem := linearOnLevels_id
  comp_mem := by
    intro F G hF hG
    exact linearOnLevels_comp hF hG
  fusion_mem := by
    intro F hmem hstable
    exact linearOnLevels_fusionLimit F hmem hstable
  m2 := by
    intro n F hF a ha hpos hskip
    exact linearOnLevels_m2 n F hF a ha hpos hskip
  m3 := by
    intro n m hnm
    exact linearOnLevels_m3 n m hnm

end BinaryWord
end SuccessorTree.NonPrecompact
