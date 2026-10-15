# Adversarial audit of the BANANA Lean formalisation — 15 October 2026

## Scope and evidential standard

Examined the complete repository tree on `main` at
`6bd119ce1943fa2eb536e6055cd7d5e1ca1c663d` (411 Lean files:
246 non-root proof modules, `BANANA.lean`, and 164 axiom-audit modules).
Also inspected the then-active pre-BANANA finite-allocation PR #223 and
the relevant open Folkman and finite-fibre PRs; compared principal
Lean declarations with the circulation `paper.tex` and its
`pre-banana.tex`, `folkman-class.tex`, `folkman-colouring.tex`,
`banana-class.tex` and `banana-eppa.tex` components.

Three separately scoped adversarial passes were used below. These
are distinct review perspectives, **not** independent model instances.
The source-level scan checked each non-root proof module for literal
`sorry`, `admit` and declared `axiom`. None occurred as proof
placeholders in that scan. This is not by itself a kernel build or a
semantic verification. The current execution environment does not have Lean/Lake installed,
so a local build was unavailable. The revised PR #223 subsequently passed
its complete Lean CI workflow, including the new finite-fibre theorem's
transitive axiom audit, and was squash-merged into `main` as
`c07b70d19b3a7d3b4c3a6f320fc36c142494e1db`.

## Referee pass I — mathematical statements and quantifiers

1. **pre-BANANA:** The actual finite class and embeddings are
   represented by marked finite Boolean algebras and by surjective
   partitions of atom sets. Finite strong AP and the persistent-colouring
   obstruction are genuinely formalised. The proposition asserting the
   countable Fraïssé limit and `ω`-categoricity is **not yet** an
   end-to-end Lean theorem. The five-ary tower provides finite stages
   and embeddings, not its full finite-extension and back-and-forth
   properties. The invariant-measure obstruction explicitly assumes
   an ambient homogeneous action, invariant presented probability
   measure and suitable finite subalgebra.

2. **Folkman–BANANA:** The atom-owner maps use `Option`, because
   non-unital Boolean-ring embeddings may leave ambient atoms unused.
   This is the correct distinction from pre-BANANA. The all-colours
   assertion fixes the ambient colouring **before** the embedded
   diagonal target, matching the circulated quantifier order. The
   two Boolean-ring sorts and pairing-preserving amalgamation are
   currently represented by related modules and open integration PRs;
   a full class-level proof must not be inferred from separate
   one-sort intersection lemmas.

3. **BANANA:** Finite structures have two F₂-vector-space sorts
   and an arbitrary possibly degenerate bilinear pairing. The explicit
   rational-coordinate limit, finite-age and global automorphism
   lemmas are formalised in that representation. The finite coherent
   extension package is not the complete class-wide coherent EPPA
   statement without the representative/transport argument. A dense
   locally finite subgroup provides the mathematical amenability
   argument, but the passage to amenability of the topological
   automorphism group is not a standalone exported Lean theorem.
   Likewise, JEP/WAP for finite systems are algebraic input to
   ample generics; the final topological theorem is a separate step.

4. **Ramsey expansions:** The persistent-colouring theorems give
   infinite *copy* Ramsey degree for the specified sources, and
   the quantified matrix-coordinate BANANA version treats sources
   with both sorts nonzero. Applying the general theorem that
   precompact Ramsey expansions bound copy Ramsey degrees is a
   separate external/theoretical step, not established just by
   counting colours.

## Referee pass II — proof dependencies and attempted counterexamples

1. The full import-root `BANANA.lean` directly imports 236
   modules. Fourteen other non-audit proof files are imported
   transitively. Directly counting files with no root import would
   give false positives. The 164 `*AxiomAudit.lean` files are
   verification entry points, not unused proof files. A local audit
   script now enumerates all of them, including those not directly
   listed as individual workflow steps.

2. **Correctness trap — total marking is not enough.** Consider a
   two-atom base with source-fibre totals `(1,1)` and target-fibre
   totals `(0,0)` in F₂. Global sums agree (both are zero), but no
   base-commuting marked allocation is possible. Per-base marking
   compatibility must be proved, not replaced by global cancellation.
   The base-compatible results in PRs #217–#222 address this gap.
   The general **single finite-fibre** result of PR #223 does not by
   itself assemble a commuting global extension.

3. The old numerical descendant-count recurrence was independent of
   the concrete word-fibre construction. Its only Lean source importer
   was `PrebananaFiveAryWordMark.lean`, which used none of its
   declarations; the root and workflow also mentioned it. The direct
   letter-reset witness proof supplies the necessary descendants.
   The count module and its audit can therefore be deleted without
   weakening any presently used theorem. Word-marking is made to
   import its actual child-marking dependency directly.

4. Earlier #223 CI identified a missing `DecidableEq β` instance
   in the **statement** of the one-parent allocation theorem
   (`Decidable (part w = b)`), before its `classical` proof could
   begin. This was an elaboration failure, not a mathematical
   counterexample. The separate one-parent theorem has subsequently
   been deleted as redundant: the remaining many-parent theorem
   subsumes it. The many-parent declaration explicitly carries
   `[DecidableEq β]`, and the revised theorem passed Lean CI.

5. An independent finite adversarial calculation checked 210
   parity-compatible allocations with 1–3 existing parents and
   1–4 target atoms, using the explicit 0/2 reset suffixes and
   residual-bin allocation. All expected total/fibre markings and
   surjectivity equations held. These tests do not prove the
   infinitely quantified extension theorem.

## Referee pass III — maintenance, code reuse, and readability

### Safe deletions/cleanups

- Remove the dead numerical descendant-count module and its audit;
  remove the corresponding root/workflow references.
- In the pending finite-allocation PR, keep the genuinely general
  finite-parent-fibre result; the separate one-parent proof and its
  audit have been removed.
- Correct stale module header descriptions of steps already proved.
- Provide explicit local axiom-audit commands and a scope/limitations
  guide in the README. **No circulation manuscript prose is changed.**

### Reuse with real downstream value

- **Already shared:** `ColouringWrappers`, residue palettes and
  `CopyRamseyDegree` serve multiple negative Ramsey-degree
  arguments; `FolkmanBilinearExtension` uses `BananaAmalgam`.
- **Promising extraction:** finite-fibre sums and sum-by-base
  cancellation in `PrebananaResidualParity`, the PR #221
  fibrewise-sum lemma and the `folkmanFiber` bi-union sums.
  A type-parametric result over a commutative additive monoid
  would serve both F₂ marks and natural-number incidence counts.
- **Promising extraction:** common image/intersection of finite
  atom partitions. It must distinguish surjective total owners
  (unital Boolean algebras) from partial `Option` owners
  (non-unital Boolean rings), including their private outside atoms.
- **Already shared / avoid duplication:** general matrix block
  amalgamation for the two-sided pairings. Do not replicate this
  construction in each of the Folkman and BANANA proofs.
- **Keep separate:** the linear-equivalence/contragredient
  automorphism constructions for BANANA contain genuine
  vector-space structure absent from pre-BANANA's finite-set
  partitions. A universal `embedding` wrapper would obscure
  rather than clarify those extra obligations.

### Outstanding proof priorities

1. Maintain the merged PR #223 kernel theorem; ensure future changes
   preserve its displayed hypotheses and axiom audit.
2. Integrate the base-compatible maps (#217–#222) with the word
   concatenation bridge (#218), proving **per-base** marking before
   asserting the finite Boolean-extension square.
3. Construct the countable pre-BANANA direct limit and prove its
   extension property, ultrahomogeneity and finite tuple orbits.
4. Finish the two-sorted Folkman strong-amalgamation wrapper
   (#171–#174) and record precisely the associated Lean theorem.
5. Separate all final group-theoretic/topological consequences from
   their finite algebraic ingredients in the validation ledger.

No independent adversary-agent run and no current local Lean build
are claimed in this report. No mathematical counterexample was found
to the checked finite combinatorial constructions; the unformalised
interfaces are still genuine obligations.
