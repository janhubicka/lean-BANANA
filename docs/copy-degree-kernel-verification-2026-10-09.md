# Kernel audit of the BANANA copy Ramsey-degree classification

Date: 9 October 2026. This note records the first successful **complete
staged** Lean check of the finite BANANA copy-degree classification.

## Verified build

GitHub Actions [run 37881218063](https://github.com/janhubicka/lean-BANANA/actions/runs/37881218063)
on commit `0653e8f0cbc7486088c09f36b641cf6b03e631f7` succeeded.
The ordinary `lake build` and the local-audit script invoked by the
workflow both completed successfully.

The audit executed and checked the transitive `#print axioms`
statements in:

- `LinePairDegreeAxiomAudit.lean`: **4 declarations**;
- `BananaCopyDegreeAxiomAudit.lean`: **5 declarations**;
- `BananaOneSidedAxiomAudit.lean`: **8 declarations**;
- `BananaOneSidedSubspaceEquivAxiomAudit.lean`: **5 declarations**;
- `BananaCopyFunctorAxiomAudit.lean`: **5 declarations**.

Every printed axiom set is contained in
`{propext, Classical.choice, Quot.sound}`.
There were no `sorryAx` dependencies or accepted unproved auxiliary
axioms. These include the terminal theorem
`BananaMatrixStructure.copyRamseyDegree_classification`,
the two-sided obstruction
`BananaMatrixStructure.copyRamseyDegree_infinite_of_positive`,
both one-sided degree-one statements, and all finite-copy palette and
representation lemmas required by their proofs.

The previously merged unconditional binary subspace Ramsey theorem is
also part of the root build. Its four-terminal-declaration GLR audit
likewise lists only these standard foundational axioms.

## Precisely what is formalised

The finite BANANA class is represented in chosen bases by two finite
binary coordinate spaces and a rectangular pairing matrix.
`BananaMatrixEmbedding` comprises injective linear maps on both
sorts preserving that pairing.

**Unlabelled copies** are represented as pairs of finite image sets,
together with proof that an embedding realises those sets; this is
independent of source automorphisms. The derived finite Ramsey
property uses colourings of these copies, not parametrised embeddings.

The theorem classifies the corresponding copy Ramsey degree:

- if at least one sort has dimension zero, degree one is available;
  degree zero is impossible (the source embeds into itself);
- if both sorts have positive dimension, no finite copy Ramsey-degree
  bound exists, even if the pairing is degenerate.

The one-sided upper bound is derived from the unconditional binary
Graham--Leeb--Rothschild theorem via the successor-tree formalisation.
The two-sided obstruction is derived directly from the persistent
intersection-residue colouring, using finite sets of colours of
line-pair subcopies and the perfect-pair extension lemma.
The exact functorial copy/subspace and palette transfer lemmas have
also passed the Lean kernel and axiom audit.

These are the statements in the **standard-coordinate presentation**
of the circulation classification theorem. An explicit Lean
equivalence with every abstract finite binary vector-space pairing
has not been packaged as a separate declaration: the standard
coordinate representation depends on choosing finite bases.

## Root integration and circulation markers

On PR #18, `BANANA.lean` now imports the checked classification,
one-sided subspace equivalences and copy functor. The PR must pass
the **root** GitHub Actions build with these new imports before
merging; successful staged compilation alone does not check their
root integration.

After the root-integrated PR is merged, the frozen circulation
manuscript may be updated **only** by replacing obsolete Lean TODOs
with pinned validation markers and updating the pinned Lean commit.
No proof sentences, theorem statements or mathematical prose may be
edited without the authors' explicit approval.

Independent adversarial referee agents were not available in this
tool environment. The mathematical desk reviews and exhaustive
small-model regressions recorded in earlier internal audit files
provide useful separate evidence but do not constitute independent
referee certification. This note claims Lean kernel checking for
the specified declarations, not a completed external referee panel.
