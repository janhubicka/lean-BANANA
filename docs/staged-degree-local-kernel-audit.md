# Local kernel audit for BANANA copy Ramsey degrees

The circulation manuscript is frozen. Only TODOs and validation markers
may be changed there; green markers must refer to declarations checked
by the Lean kernel.

## Current position

The following files are staged in `main` but are deliberately not
imported by root `BANANA.lean`:

- `LinePairEmbeddingDegree.lean`, `LinePairExtension.lean`,
  `BananaEmbeddingDegree.lean`: transfer persistent line-pair
  colourings to embedding-degree obstructions.
- `BananaCopyRanges.lean`, `BananaCopyPalette.lean`,
  `BananaCopyDegree.lean`: direct, automorphism-invariant
  *unlabelled copy* degree obstruction for every two-sided source.
- `BananaOneSidedCopyRanges.lean` and
  `BananaOneSidedCopyDegree.lean`: transfer the successor-derived
  binary GLR theorem to copy degree one when either sort is zero;
  exclude degree zero and state the classification.
- `BananaOneSidedSubspaceEquiv.lean`: bijections between one-sided
  copies and fixed-dimensional subspaces of the nonzero sort for
  **every** ambient BANANA pairing.

The GLR successor-tree derivation was independently built and merged
through PR #7. The subsequent modules above were committed as
**uncompiled source** and must not be described as kernel-verified.

## Local build procedure

From the `lean-BANANA` repository root, with the pinned Lean/Lake
toolchain and dependencies installed, run:

```sh
bash scripts/check_staged_ramsey_degrees.sh
```

The script builds the four transitive axiom-audit modules and then
runs Lean on each `#print axioms` file. It requires outputs for each
requested declaration, rejects any unexpected axiom (including
`sorryAx`) and exits without a success message if any build or
audit fails. Logs are in `.lake/banana-audit/` by default, or the
directory named by `BANANA_LEAN_AUDIT_LOGDIR`.

The only permitted axiom dependencies for these declarations are
`propext`, `Classical.choice` and `Quot.sound`. If Lean changes
how it prints axioms, adapt the parser conservatively; never treat
missing axiom output as success.

No GitHub Actions or remotely budgeted runners are used. Because this
assistant's container has no `lake` binary and cannot resolve
GitHub, the script has only been syntax-checked locally, not run
through the compiler. Its explicit no-`lake` failure path has been
tested (exit code 2).

## Promotion after successful checking

1. Resolve all elaboration/build failures **in small, local commits**.
2. Review exact statement correspondence with the circulation
   `thm:banana-degree-classification`, including the quotient of
   embeddings by source automorphisms already represented by
   `BananaCopyRanges`.
3. Re-run the complete local audit and record the pinned commit SHA,
   all axiom outputs, and an independent adversarial proof review.
4. Only then add the verified modules to root `BANANA.lean` and
   insert precise green `\leanverified` markers. Any suggested
   manuscript wording changes must remain `\todo` notes unless
   the authors explicitly approve changing frozen prose.

Until step 3, the circulation TODOs inserted by BANANA PRs
#162 and #164 remain appropriate.
