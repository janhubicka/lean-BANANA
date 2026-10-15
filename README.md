# lean-BANANA

Lean 4 formalisation supporting the **BANANA** manuscript. The circulation
manuscript is maintained separately in [janhubicka/BANANA](https://github.com/janhubicka/BANANA).
Its circulation text is frozen: mathematical corrections should be proposed
as TODOs, not silently applied.

The library is organised around three related, but **different**, classes.
In particular, unital Boolean-algebra embeddings in pre-BANANA must not be
confused with non-unital Boolean-ring embeddings in Folkman–BANANA.

## Source map and proof status

The following is a guide to the proof statements, not a claim that every
consequence in the paper is already a theorem of Lean.

| Development | Established in the Lean sources | Further obligations |
| --- | --- | --- |
| **pre-BANANA** | Finite marked Boolean-algebra models; atom-powerset representations; marked embeddings; finite strong amalgamation, heredity and joint embedding; obstruction to EPPA; persistent copy colourings and infinite copy Ramsey degree; five-ary finite stages, marking-preserving connecting embeddings and residual-parity lemmas | A complete finite-extension diagram, countable homogeneous Fraïssé limit and its Stone/topological actions. The measure obstruction is conditional on the stated representation and homogeneity hypotheses |
| **Folkman–BANANA** | Non-unital atom-owner representation; individual Boolean-ring-sort amalgamation and exact image intersection; bilinear block-extension calculations; persistent copy colourings and infinite copy Ramsey degree | Combined two-sorted, pairing-preserving strong amalgamation and finite-age/limit conclusions need the remaining integration work |
| **BANANA** | Bilinear-pairing matrix models, perfect completion and finite amalgamation; explicit countable pairing, finite age, finite-substructure homogeneity and finite tuple-orbit criteria; locally finite finite-GL approximation; algebraic constituents of coherent EPPA; persistent colourings and copy Ramsey degrees | Final group-theoretic deductions (including topological amenability and ample generics) and the finite representative bookkeeping for a fully packaged coherent-EPPA assertion are not all expressed as end-to-end Lean theorems |

Some theorems are stated in standard finite coordinates or as conditional
interfaces. Their hypotheses must be checked when using them to justify a
manuscript proposition. In particular, a theorem about an invariant
probability mass is not itself an existence theorem for a Stone action.

The principal files are under `BANANA/NonPrecompact/`:
`PrebananaFiniteBooleanModelStrongAP.lean`,
`PrebananaCopyDegree.lean`,
`PrebananaExplicitFiveAryTower.lean`,
`FolkmanAtomAmalgam.lean`,
`FolkmanPersistence.lean`,
`BananaStructure.lean`,
`BananaLimitGlobalHomogeneity.lean`,
`BananaLimitLocallyFiniteDense.lean`,
`CoherentEppaPackage.lean`, and
`BananaCopyDegree.lean`.

For the five-ary extension proof, start with
`docs/prebanana-five-ary-fraisse-construction.md`. The finite-parent-fibre allocation theorem was verified and merged
via [PR #223](https://github.com/janhubicka/lean-BANANA/pull/223).
The full common-base-commuting finite extension is still open.

## Local verification

Use the toolchain in `lean-toolchain` and the dependencies pinned by
`lakefile.toml`. From a checkout with Lean/Lake installed:

```sh
lake build BANANA
bash scripts/audit_all_axioms_local.sh
```

The first command compiles the library. The second runs
`scripts/check_lean_module_graph.py`, compiles every
`*AxiomAudit.lean` entry point, and checks each printed transitive
axiom set against **exactly** `propext`, `Classical.choice`, and
`Quot.sound`. Unexpected axioms (including `sorryAx`) make the audit
fail. This proves neither theorem-statement fidelity nor the
remaining conditional hypotheses in the manuscript.

Run `python3 scripts/check_lean_module_graph.py` separately to report
unreachable source modules, missing local imports, import cycles,
and empty axiom-audit entry points without invoking Lean.

There are small independent finite regression scripts in `scripts/`;
these supplement, but do not replace, Lean kernel checks. For the
current adversarial findings, scope restrictions and maintenance
decisions see
`docs/formalisation-adversarial-audit-2026-10-15.md`.

## Reusable tools

The existing development already shares the `F2` residue palette,
subset-sum arguments and copy-colouring definitions. The Folkman
bilinear extension also reuses the BANANA zero-cross-block matrix
amalgamation rather than maintaining a second matrix construction.

A worthwhile further extraction is a **finite-fibre calculus** for
disjoint blocks, inverse-image maps, sum decomposition and preservation
of prescribed markings. It should accommodate both total surjective
owner maps (pre-BANANA) and partial `Option`-valued owner maps
(Folkman–BANANA). The `Option.none` fibres are essential and cannot
be erased by declaring the two classes' embeddings equivalent.
Matrix pairing preservation is a further condition, not a consequence
of marked finite-set allocation.

Keep the small, concrete instances in use until a common lemma has at
least two genuine downstream applications. Historical attempts can be
recovered from Git rather than retained as unused parallel APIs.
