# Track D — coherent EPPA and automorphism-group validation

Internal development note, 1 November 2026. No circulation text changed.
Parent track-A plan: docs/banana-circulation-parallel-validation-plan-2026-11-01.md,
currently staged in draft PR #307; no dependency on its unmerged branch. Branch base: lean-BANANA main at 7bbfc5846a0223c9028aa50dc442aef88ce3f01a.

## Exact statement audit

| Manuscript claim | Lean evidence | Verdict |
| --- | --- | --- |
| Theorem thm:eppa, coherent EPPA with both witness dimensions l+r | Completion/PerfectHomogeneity, CoherentEppaPackage.exists_alignedCoherentAmbientAction, CoherentConjugation.* | Constituents only. Finite representative-choice/transport for every substructure is not an end-to-end declaration. Do not mark the theorem fully Lean-verified. |
| Proposition prop:amenable, dense increasing union of finite subgroups | BananaLimitFiniteGLStages, BananaLimitFiniteGLStageInclusions, BananaLimitDirectedGLUnion, BananaLimitLocallyFiniteDense.bananaLimitFiniteGLUnion_pointwise_approximates | Finite stage, finite-family common stage and algebraic finite-neighbourhood criterion are explicitly stated. The choice of a cofinal countable exhaustion, the topology/actual Aut(M) bridge, and the amenability deduction are external/unformalised. |
| Theorem thm:ample-generics, all finite n-system JEP/WAP | BananaFiniteSystemsJepWap.bananaFiniteSystems_jep_and_wap | Exact finite-system algebraic input present; the Kechris–Rosendal dynamical implication remains external. |

### New isolated bridge

CoherentEppaRepresentativeTransport.lean proves, **conditionally**, that
g_V rho(h) g_U^{-1} extends the representative action simultaneously on
the two sorts whenever (i) rho is a genuine group homomorphism,
(ii) rho(h) acts correctly on the fixed base copy of both sorts and
(iii) g_U, g_V carry both base copies to the chosen copies.

CoherentRepresentativeCore.lean separately defines the two-sort
representative code i_V^{-1} p i_U for arbitrary carrier equivalences,
and proves the identity and composition law with the correct (reversed)
permutation multiplication order. A separate theorem shows that the code
preserves the pairing *provided* the selected representative identifications
and the original two-sorted isomorphism preserve it. Linearity remains a
separate obligation, as do the concrete BANANA automorphism-group interface
and finite representative choices. The extension bridge is likewise conditional,
not the finite selection of all U0 and i_U nor the group construction. CoherentConjugation already proves
identity, inverse and group law. Never infer the full coherent EPPA
conclusion from the new conditional bridge alone.

### Remaining end-to-end work

1. Define the two-sorted pairing-preserving automorphism group of an
   arbitrary finite representative U0, with multiplication agreeing with
   the existing LinearEquiv.trans conventions. Include empty left/right
   sorts, zero pairing and proper subspaces. Connect the existing
   completion-action identity/composition lemmas to a genuine group hom.
2. For every isomorphism class of substructures of fixed finite A, select
   a representative U0 and prove a dimension-bounded aligned embedding
   of its completion in the SAME perfectBanana (l+r) witness. Carry the
   representative identifications on both sorts.
3. For each U isomorphic to U0 choose a pairing-preserving ambient
   conjugator g_U whose restrictions are the prescribed identifications,
   and construct the core representative automorphism for each p:U→V.
   Verify on both sorts that core(q o p)=core(q)*core(p), in the
   multiplication convention used by the ambient group.
4. Apply the new transport bridge to show Theta(p) extends p on U.
   Combine with CoherentConjugation to prove a single class-wide
   coherent-EPPA theorem, with the bound dim(B_L)=dim(B_R)=l+r.
5. For amenability: formalise if desired the countable cofinal sequence
   of rational support sets and a topology-compatible dense-subgroup
   interpretation. The implication 'locally finite dense subgroup
   => topological amenability' may remain a clearly cited external
   theorem, not an unmarked Lean conclusion.
6. For ample generics: audit the definitions of n-systems and their
   embeddings against Kechris–Rosendal, then invoke the external
   theorem only after confirming the hypotheses (Fraisse limit,
   Polish automorphism group, all n-system JEP/WAP).

## Adversarial reviews

Referee A — statement fidelity:
* The currently packaged EPPA theorem is conditional on a fixed
  finite structure, an embedding j and an arbitrary ambient embedding E0.
  It does not quantify over all partial automorphisms of A together with
  coherent choices. The new transport lemma is similarly conditional.
* The finite-stage union is a SET of pairs of linear equivalences.
  Algebraic closure, common finite-stage containment and approximation
  do not themselves implement pointwise-convergence topology or the
  standard amenability theorem.
* JEP and WAP for every n are genuinely stated in
  bananaFiniteSystems_jep_and_wap, not merely as a single n test.

Referee B — counterexample and boundary tests:
* Suppressing base-copy equivariance invalidates the extension claim
  even with g_U=1 and a nonidentity representative automorphism.
* Composition must use the noncommutative order Theta(q)Theta(p), not
  Theta(p)Theta(q); no change in ordering is allowed when modelling
  LinearEquiv.trans as group multiplication.
* Two ambient sorts must be tested independently, including a
  contragredient second action, empty sorts, degenerate matrices,
  and representatives U,V with distinct chosen conjugators.
* Arbitrary changes of representative coordinates need not preserve even
  the one-dimensional F2 pairing. The new pairing theorem explicitly
  requires preservation by both selected identifications and p.
* Coherent partial automorphisms are defined only between isomorphic
  source and range substructures. A class-wide formulation must not
  assume arbitrary independently chosen homomorphisms between objects.

These are two separate *logical audit passes*, not independently
spawned reviewers and not a Lean kernel verification.

## Finite regressions (run locally in Python, not Lean)

* scripts/check_coherent_representative_transport.py: S3 in S4,
  20,736 two-sort extension checks, 497,664 noncommutative composition
  checks, 3,456 inverse checks. Negative test for omitting the
  base-copy equivariance hypothesis.
* scripts/check_coherent_representative_core.py: 15,552 two-sort
  representative-code composition checks in S3, using independent
  changes of coordinates on the right sort, plus a one-dimensional
  counterexample when a coordinate change fails to preserve pairing.
* scripts/check_coherent_eppa_small_pairings.py: all 17 bilinear
  matrices with l+r<=3, all 1,277 partial two-sorted linear
  isomorphisms, all extend in perfect dimension l+r. This checks
  ordinary EPPA only; coherent choices are NOT checked.

## Local kernel gate before merge or verification marker

There is no Lean/Lake executable in the current runtime and GitHub
runners are out of budget. This branch is DRAFT / UNVERIFIED.

At the *exact* PR head, run:
1. python3 scripts/check_lean_module_graph.py
2. lake env lean BANANA/NonPrecompact/CoherentEppaRepresentativeTransport.lean
3. lake env lean BANANA/NonPrecompact/CoherentEppaRepresentativeTransportAxiomAudit.lean
4. lake env lean BANANA/NonPrecompact/CoherentRepresentativeCoreAxiomAudit.lean
5. lake build BANANA
6. bash scripts/audit_all_axioms_local.sh
7. python3 scripts/check_coherent_representative_transport.py
8. python3 scripts/check_coherent_representative_core.py
9. python3 scripts/check_coherent_eppa_small_pairings.py

Only propext, Classical.choice and Quot.sound are permitted in the
transitive axiom results. Inspect exact theorem binders and assumptions
separately. Do not merge without the exact-head local build and audits.
No changes to any TeX file or to BANANA.lean in this track.
