# Track D continuation: typed coherent transport

Internal development note; not circulation prose. Base: PR #310 at
`3f574899cd0f0b10e902408003dee6c6150f6f59`.

**Status: DRAFT / NOT KERNEL-CHECKED.** No independent model referee was
available. The checks below are a source review by the implementing assistant
and genuinely executed finite Python regressions, not independent sign-off.
No TeX, manuscript annotations, root imports or other tracks were changed.

## Source defect repaired

The staged `BananaMatrixCompletionActionHom.lean` qualified the definition
`dotContragredient` as `BananaMatrixStructure.dotContragredient`. Its definition
in `PerfectHomogeneity.lean` is in `SuccessorTree.NonPrecompact`, not the
nested namespace. Use that definition directly. The associated `_refl` and
`_trans` lemmas really are in `BananaMatrixStructure` and retain their
qualification. Identity/composition proofs now use the existing equivalence
lemmas directly, with the multiplication order made explicit.

This repairs an identified source-level defect; it is not evidence that the
entire module now elaborates. No Lean compiler was available for that check.

## New finite-algebra interfaces

* `BananaMatrixRepresentativeIso.lean`: an isomorphism consists of two linear
  equivalences preserving the pairing. Identity, inverse and composition keep
  these properties. The coordinate map `i_V^{-1} p i_U` therefore lands in
  `BananaMatrixAutGroup A`, with no extra unproved linearity hypothesis. The
  module records compatibility with the earlier carrier-permutation code,
  its two coordinate identities, and its identity/composition/inverse laws.
* `BananaMatrixEmbeddedCompletionHom.lean`: finite self-embeddings are converted
  to the actual automorphism subgroup without changing either action. The
  existing embedded-completion action is then packaged as a group
  homomorphism. `exists_bananaMatrixAlignedCompletionHom` supplies one such
  homomorphism extending all automorphisms of a representative, provided the
  original aligned-completion embedding hypotheses hold.
* `BananaMatrixCoherentTransport.lean`: the formula
  `g_V rho(code(p)) g_U^{-1}` now operates on actual BANANA isomorphisms and
  actual BANANA automorphism groups. It has identity, composition and inverse
  statements and one extension theorem covering both sorts simultaneously.
* `BananaMatrixCoherentTransportAxiomAudit.lean`: 20 transitive-axiom queries
  covering the new definitions and statements, including finite conversion
  and the aligned homomorphism. These queries have NOT been run in Lean.

These are staged proof scripts, not newly validated declarations. They reuse
`CoherentConjugation` and the existing completion-action lemmas. No global
instances for arbitrary permutations or actions have been introduced.

## Statement-fidelity and boundary review

The old obligation to turn an arbitrary permutation code into a linear,
pairing-preserving automorphism is addressed by making the chosen maps
`BananaMatrixIso` from the outset. The carrier-level compatibility theorem
ensures this is the same coordinate formula, not a different encoding.

The extension theorem requires the SAME conjugator to align the left and
right representative copies. The group homomorphism must also extend BOTH
sorts. Neither condition follows from checking the other sort alone. No
nondegeneracy hypothesis is imposed on the representative pairing.

`p.trans q` means q after p. The group product is therefore code(q) * code(p).
The two expressions agree by cancellation of the intermediate representative
identification. Extension follows by writing a domain point as i_U(x),
cancelling g_U^{-1}g_U, applying rho's extension identity, and then applying
the coordinate identity for i_V. The same argument is separately stated for
the right sort. Zero-dimensional sorts contain their zero vector; they are
not empty sets.

## Actual finite experiment: simultaneous choices

`scripts/check_banana_coherent_choices.py` is a new standalone regression,
not a claim that the four older scripts have been rerun. It enumerates all
17 F2 pairing matrices with l+r <= 3. For each pairing it uses ONE perfect
witness of side dimension l+r, chooses one representative per actual
isomorphism class of subpairs, aligns its perfect completion, fixes one
identification and conjugator per object, and constructs the whole extension
assignment from those fixed choices.

Executed successfully with Python 3.13.5, both normally and with `-O`:

| Quantity | Count |
| --- | ---: |
| Pairing matrices | 17 |
| Subpairs and identity checks | 135 |
| Isomorphism classes, summed over matrices | 81 |
| Representative automorphisms used in the homomorphisms | 491 |
| Partial isomorphisms and inverse checks | 1,277 |
| Composable pairs, checked on both sorts | 82,697 |
| Negative controls | 2 |

Every assigned extension is checked to be an ambient linear automorphism.
The right action is its contragredient. Restrictions, identities, inverses
and composition are checked on both sorts. The 491 representative actions
are not the same statistic as the older 377 original-structure automorphisms.

The checks remain active under `python -O`; they use an explicit exception,
not Python assert statements. An additional deliberately reversed transport
formula was run locally and rejected by the extension test. The exact
script hash and results are in
`docs/track-d-coherent-choices-results-2026-11-02.json`.

This tests a complete finite coherent assignment in the enumerated cases.
It does NOT prove the universal coherent-EPPA theorem or type-check Lean.

## Remaining universal construction

1. Represent every actual substructure of a fixed finite A in the typed
   isomorphism interface, with a single representative chosen for each
   isomorphism class. Do not assume all substructures have one common type.
2. Construct the representative's aligned homomorphism and every conjugator
   in the SAME perfect completion of A. Discharge the natural-number
   dimension inequalities and coordinate transports; the final side
   dimension must be dim(A_L)+dim(A_R), not a new bound per arrow.
3. Assemble the maps over all isomorphism classes into ONE assignment on
   actual partial automorphisms. Export extension and the coherent-triple
   law together, with the exact manuscript witness bound.
4. Compile the exact head, audit all transitive axioms, and obtain genuinely
   independent statement-fidelity and counterexample reviews before merging
   or adding a verification marker. Existing topological consequences remain
   outside this finite-algebra change.

## Local verification gate

No GitHub Actions should be started. In a checkout with the pinned toolchain:

```sh
python3 scripts/check_lean_module_graph.py
lake build +BANANA.NonPrecompact.BananaMatrixCoherentTransportAxiomAudit \
  +BANANA.NonPrecompact.BananaMatrixCompletionActionHomAxiomAudit \
  +BANANA.NonPrecompact.CoherentEppaRepresentativeTransportAxiomAudit
lake env lean BANANA/NonPrecompact/BananaMatrixCoherentTransportAxiomAudit.lean
lake build BANANA
bash scripts/audit_all_axioms_local.sh
python3 scripts/check_banana_coherent_choices.py
python3 -O scripts/check_banana_coherent_choices.py
```

The explicit module targets build the new imports without editing the root
file. Lake documents `+Module` as a module target in its official build-tool
reference. Only `propext`, `Classical.choice` and `Quot.sound` may occur in
the transitive axiom reports. A successful finite regression is not a merge
gate substitute. The local runtime lacked Lean/Lake; fetching the pinned
release was also unavailable. No build, kernel audit or independent review
success is claimed in this batch.
