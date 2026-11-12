# Adversarial check of the unindexed coherent-EPPA transport

Internal Lean-validation note, 12 November 2026. **Not circulation prose.**
Base: Track D PR #310 at \`f36273cdfb4e2681c1f19dd49f9d46b9ec0b8a2b\`.

## Exact mathematical interface

The proposed terminal result \`exists_bananaActualCoherentEPPA\` in
\`BananaActualSubpairUnindexedCoherence.lean\` has a genuinely unindexed
arrow map: for each finite two-sorted pairing \`A\` of dimensions \`l,r\`,
there is a single assignment taking every actual pairing-preserving
isomorphism \`p : U ≃ V\` of pairs of vector subspaces to an automorphism
of \`perfectBanana (l+r)\`. Its four postconditions are identity,
composition, inverse and extension on both left and right actual vectors.
No nondegeneracy or nonzero-sort assumption is present.

The supporting atlas chooses one coordinate presentation **per actual
subpair**, rather than once per arrow. The quotient class uses existence
of an actual two-sorted pairing isomorphism. Every actual arrow therefore
equates its endpoint classes. Dependent class-index transport changes
only proofs of quotient membership, not the ambient automorphism.

For a fixed class choose a representative \`A_c\`, isomorphisms
\`i_U : A_c -> U\`, a group homomorphism
\`rho_c : Aut(A_c) -> Aut(B)\` extending representative automorphisms, and
ambient conjugators \`g_U\` aligning the representative with each
embedded copy. The candidate transport is

\`\`\`text
Theta(p : U -> V) = g_V * rho_c(i_V^{-1} * p * i_U) * g_U^{-1}.
\`\`\`

With multiplication interpreted as function composition, the middle
terms for consecutive arrows cancel:
\`i_W^{-1} q i_V i_V^{-1} p i_U = i_W^{-1} (qp) i_U\`.
So \`Theta(q) Theta(p) = Theta(qp)\`; identity and inverse follow from
the same fixed objectwise choices and the homomorphism property.
Different class choices need not produce equal ambient automorphisms,
but **each fixed choice** must be coherent. Claims of canonical
uniqueness would be unjustified and are not present in the Lean theorem.

The source-level dependencies are:
\`BananaPresentedSubpairAtlas\`,
\`BananaActualSubpairCoordinates\`,
\`BananaActualSubpairFunctor\`,
\`BananaMatrixCoherentOneClass\`,
\`BananaMatrixCoherentClassFamily\`,
\`BananaActualSubpairClassCoherence\`,
\`CoherentGroupoidDescent\`, and
\`BananaActualSubpairUnindexedCoherence\`.
The source-level argument is mathematically consistent with the
circulation formulation of coherent EPPA (actual partial isomorphisms,
not arbitrary permutations), **conditional on Lean elaborating the exact
definitions and the earlier perfect-pairing extension lemmas**.

## Independently structured finite regression

Run:

\`\`\`sh
python3 scripts/check_banana_groupoid_descent_adversarial.py
python3 -O scripts/check_banana_groupoid_descent_adversarial.py
\`\`\`

The script uses the full group GL(3,2) of 168 linear maps and GL(2,2)
of six maps. The objects are **all** actual zero-, one- and
two-dimensional subspaces of F_2^3 (1, 7 and 7 objects). It chooses
two different systems of objectwise conjugators, assigns three distinct
class labels, builds the corresponding labelled maps, and descends
them by each object's class. Every arrow is checked to extend the
actual source-to-target subspace map. It checks identities, inverses,
composition and invariance under relabelling.

Both the normal and optimised Python runs passed:

\`\`\`text
arrows                  2064
classes                    3
composable_pairs       76152
identity                  90
inverse                 2064
label_assignments        18
reindexing_comparisons  2064
wrong_formula_rejected     5
\`\`\`

A deliberately incorrect \`g_V rho(a) g_U\` formula was rejected
by the identity control. These test counts include repeated class
labellings; they are not 76,152 mathematically independent pairings.

## What this does NOT establish

* The finite test is of the **abstract groupoid transport** using GL(3,2),
  not a test of the full two-sorted BANANA pairing or the construction of
  an aligned perfect-completion action. Prior separate finite BANANA
  checks address those ingredients.
* It is **not** a full exact-head Lean build. The current container has
  neither Lean/Lake nor DNS access to clone the pinned repository
  dependencies. No GitHub Actions runner was used.
* The proposed terminal Lean theorem may still have elaboration or
  typeclass errors. Every named axiom-audit module must compile and
  its printed transitive axioms must be inspected, not inferred from
  a syntactic search for \`sorry\`.
* This is an independent *test implementation*, not an independently
  spawned human or model referee and not a substitute for a second
  theorem-statement audit.
* The manuscript is frozen. No green marker for the **whole** coherent
  EPPA theorem is justified until the exact-head local build and
  independent fidelity reviews pass. No TODO removed or commented
  out by Sofia has been restored.

## Remaining release gate

On a complete checkout of the exact PR #310 head, with pinned
Lean \`v4.35.0-rc3\` and its exact dependencies:

\`\`\`sh
python3 scripts/check_lean_module_graph.py
lake build BANANA.NonPrecompact.BananaActualSubpairUnindexedCoherence
lake env lean BANANA/NonPrecompact/BananaActualSubpairUnindexedCoherenceAxiomAudit.lean
lake build BANANA
bash scripts/audit_all_axioms_local.sh
python3 scripts/check_banana_groupoid_descent_adversarial.py
\`\`\`

Then compare the fully elaborated \`#check exists_bananaActualCoherentEPPA\`
type, including implicit hypotheses, to the printed coherent-EPPA
statement, independently audit both the source embedding notion and
the dimension bound, and only then reconsider the Track D merge.
