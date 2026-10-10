# Internal adversarial audit — finite GL stages and density
10 October 2026. Not part of the circulation manuscript.

## Algebraic review: fixed stages

For each finite support S, GL(F₂^S) acts on the left of the perfect pairing and by the inverse transpose on the right. Two adversarial checks:

1. A left automorphism alone is insufficient: the right action MUST be the contragredient. The two-sided pairing-preservation lemma in `BananaLimitFiniteGLAction.lean` supplies that obligation.
2. Closure of a stage under multiplication does not by itself prove that it is a subgroup: identity and inverse closure are separately required. `BananaLimitFiniteGLStages.lean` checks finiteness, identity, composition and inverses, as well as the finite-stage action laws.

The stage calculations were kernel-checked before considering a directed union.

## Geometry and density review

The density argument must not assume that an arbitrary automorphism sends a whole finite *coordinate block* to itself. Given finite test families F_L and F_R, instead take their generated finite subspaces, realise their exact ranges by an embedded finite BANANA structure, transport that embedding by the global automorphism, then apply finite perfect-pair homogeneity inside a common block containing both images. This is the route formalised by `BananaLimitFiniteGLDensity.lean`, merged after full Lean checks.

There is an additional issue with nesting: `bananaLimitBlockStandardEquiv S` and `bananaLimitBlockStandardEquiv T` choose their finite enumerations independently. Thus one must NOT identify GL(S) with an upper-left matrix corner of GL(T) without conjugating the choices. The candidate theorem `exists_bananaLimitFiniteGLAction_larger_stage` instead restricts the actual global action to the T-supported subspace, conjugates it to the standard T coordinates and uses perfect-pair nondegeneracy to recover the right contragredient. The final global equality follows from the extend–restrict identity. This candidate is NOT marked verified until its Lean build and transitive axiom audit succeed.

## Small finite-model adversarial checks

A separate exhaustive binary bitset calculation checked all invertible matrices of dimensions n=0,1,2,3, with GL counts 1,1,6,168. The inverse-transpose pairing law passed 10,853 tests over these dimensions.

For a four-coordinate ambient block, each subset S of size at most three and each invertible transformation on S was extended by the identity on the other coordinates, without assuming S consecutive. The induced full matrix and its inverse transpose were checked against the direct finite-support actions on every ambient vector: 22,816 separate equalities passed.

These checks are finite regressions, **not** proofs of the infinite statements and **not** independently spawned referees. The mathematical audit and Lean kernel remain distinct evidence.

## Remaining obligations

- Lean validation/merger of T-block restriction, fixed outside-component, extend–restrict and nested-stage parameter transport results (draft PRs #54, #56, #57, #58).
- Explicitly assemble the directed union of finite subgroups and interpret the finite-set approximation lemma as density in the pointwise convergence topology, or cite the standard general topology lemma.
- Apply the standard facts that locally finite discrete groups are amenable and a topological group with a dense amenable subgroup is amenable. These are not currently Lean-formalised and should not receive green validation markers.

Only validation markers and TODO notes may be added to the frozen circulation text.
