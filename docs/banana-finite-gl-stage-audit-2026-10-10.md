# Internal adversarial audit — finite GL stages and density
10 October 2026. Not part of the circulation manuscript.

## Algebraic review: fixed stages

For each finite support S, GL(F₂^S) acts on the left of the perfect pairing and by the inverse transpose on the right. Two adversarial checks:

1. A left automorphism alone is insufficient: the right action MUST be the contragredient. The two-sided pairing-preservation lemma in `BananaLimitFiniteGLAction.lean` supplies that obligation.
2. Closure of a stage under multiplication does not by itself prove that it is a subgroup: identity and inverse closure are separately required. `BananaLimitFiniteGLStages.lean` checks finiteness, identity, composition and inverses, as well as the finite-stage action laws.

The stage calculations were kernel-checked before considering a directed union.

## Geometry and density review

The density argument must not assume that an arbitrary automorphism sends a whole finite *coordinate block* to itself. Given finite test families F_L and F_R, instead take their generated finite subspaces, realise their exact ranges by an embedded finite BANANA structure, transport that embedding by the global automorphism, then apply finite perfect-pair homogeneity inside a common block containing both images. This is the route formalised by `BananaLimitFiniteGLDensity.lean`, merged after full Lean checks.

There is an additional issue with nesting: `bananaLimitBlockStandardEquiv S` and `bananaLimitBlockStandardEquiv T` choose their finite enumerations independently. Thus one must NOT identify GL(S) with an upper-left matrix corner of GL(T) without conjugating the choices. The theorem `exists_bananaLimitFiniteGLAction_larger_stage` instead restricts the actual global action to the T-supported subspace, conjugates it to the standard T coordinates and uses perfect-pair nondegeneracy to recover the right contragredient. The final global equality follows from the extend–restrict identity. The theorem has passed its Lean root build, dedicated transitive-axiom audit and complete CI workflow, and was merged in PR #58.

## Small finite-model adversarial checks

The reproducible script `scripts/check_nested_banana_gl_small.py` in PR #60 exhaustively checks all **713** invertible binary transformations on the subsets S of a four-coordinate ambient block with |S| at most three (GL(0,2), GL(1,2), GL(2,2), GL(3,2) have orders 1, 1, 6 and 168). It performs **182,528** pairing-preservation comparisons on all left/right ambient vector pairs.

For every S⊆T, independently scrambled coordinate enumerations are used for S and T. The script constructs the induced T-block left transformation and its inverse transpose, and compares both globally lifted actions on every ambient vector: **49,152** component-action equalities pass. The Python regression step has passed CI. These counts supersede earlier informal illustrative counts that were not retained in a reproducible test.

These checks are finite regressions, **not** proofs of the infinite statements and **not** independently spawned referees. The mathematical audit and Lean kernel remain distinct evidence.

## Remaining obligations

- The nested-block restrictions, fixed outside components, extend–restrict identity and finite-stage inclusion theorem are merged and Lean-verified (PRs #54, #56, #57, #58). The directed-union local-finiteness theorem was subsequently kernel-verified and merged (PR #59).
- Complete verification/merger of the combined finite-set approximation theorem for that directed union (PR #61); the underlying finite-set approximation theorem itself was previously merged.
- Interpret the concrete finite-set approximation statement as density in the pointwise convergence topology, citing the standard general topology fact if it is not Lean-formalised.
- Apply the standard facts that locally finite discrete groups are amenable and a topological group with a dense amenable subgroup is amenable. These are not currently Lean-formalised and should not receive green validation markers.

Only validation markers and TODO notes may be added to the frozen circulation text.
