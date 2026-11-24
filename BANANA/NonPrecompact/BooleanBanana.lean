import BANANA.NonPrecompact.PrebananaCopyDegree
import BANANA.NonPrecompact.PrebananaFiniteBooleanModelStrongAP
import BANANA.NonPrecompact.PrebananaFiveAryCylinderMarkedOrbitFiniteness

/-!
# Boolean–BANANA

The manuscript's class `𝒦_bool` consists of finite nontrivial Boolean
algebras with an admissible disjoint-additive parity map `μ`. Its
embeddings preserve `μ` and the Boolean operations, including the constants.
Lean writes join and meet as `⊔` and `⊓`.

This entry point gives the finite models and the countable cylindrical
presentation of `M_bool` names matching the manuscript. The underlying
declarations remain available at their original source locations.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

/-- A finite model in the manuscript's class `𝒦_bool`. -/
abbrev FiniteModel := PrebananaFiniteBooleanModel

/-- A unital marking-preserving Boolean-algebra embedding. -/
abbrev Embedding (A B : FiniteModel) := PrebananaFiniteBooleanEmbedding A B

/-- The explicit countable cylinder model for `M_bool`. -/
noncomputable abbrev limit := prebananaCylinderCountableModel

/-- The atom-coordinate presentation of `B_bool(q)` for `q = 2^(k+1)`. -/
abbrev allMarkedTarget (k : ℕ) := PrebananaAtomStructure.allMarkedPower k

alias strongAmalgamation := prebananaFiniteBooleanModel_strongAmalgamation

alias finiteModel_embeds_limit := prebananaCylinder_allFiniteModels_embed

alias finiteSubmodel_factors := prebananaCylinder_finiteSubmodel_factor

alias limit_automorphism_extends := prebananaCylinder_exists_global_marked_boolean_automorphism

alias limit_tupleOrbits_finite := prebananaCylinderMarkedOrbit_finite

alias atomCoordinate_copyDegree_infinite := prebananaTwoMarkedCopyRamseyDegree_infinite

end SuccessorTree.NonPrecompact.BooleanBanana
