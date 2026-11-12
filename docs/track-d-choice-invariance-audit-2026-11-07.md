# Track D: adversarial audit of representative choices (7 November 2026)

This is an **internal validation note**, not circulation prose. No TeX, TODO
or validation-marker changes have been made. The Lean proof scripts in
PR #310 remain **uncompiled and not kernel-verified**.

## Merge safety

At the time of this audit, main was
`ba5eb4de92bef50708cd226fcda6b2c01baf8051`.
The draft feature branch inherited main via merge commit
`d59af3a7f6d269bb555eb87589d8264411f4b96c`.
We constructed the merge tree from all 620 mainline blobs and all 40
Track-D-only blobs, comparing SHA-1 content identities before moving the
branch. The five overlapping verifier files were identical. The three
further differing files on main (root `BANANA.lean`, pre-BANANA fibre
sums, README) were mainline-only changes and were retained from main.
No conflicts and no manuscript changes.

This merges main *into the draft branch only*. The unverified Track D code
is NOT merged into main.

## Representative-choice audit

Let I be the set of actual isomorphism classes of finite subpairs of A.
For each class i fix one representative U_i and an embedding in a
common perfect witness B_(l+r). For each object U in i, fix one
isomorphism a_U: U_i -> U and one ambient conjugator g_U extending a_U.
With the representative homomorphism rho_i, define the extension for an
arrow p: U -> V by

    Theta(p) = g_V rho_i(a_V^{-1} p a_U) g_U^{-1}.

This assignment is coherent *for any choices that are held fixed per
class and per object*. Its actual value need not be independent of those
choices. The manuscript does not require uniqueness; it requires one
coherent extension function. Changing the representatives, alignments
and conjugators may change that function, without invalidating the
coherence and extension laws.

The key logical dependencies are:

1. A single representative U_i must be used throughout each isomorphism
   class. An arbitrary 'latest previously encountered isomorphic object'
   policy depends on U and is not a valid class representative choice.
2. A single isomorphism a_U and one ambient g_U must be fixed for each
   object U. Choosing independently for each *arrow* can destroy
   cancellation at the intermediate object V.
3. The same g_U must act on both sorts; separate left/right ambient
   transformations need not form a pairing-preserving automorphism.
4. The homomorphism rho_i must be defined on the actual automorphism
   group of U_i and preserve composition; an arbitrary set-theoretic
   extension of each individual automorphism would not suffice.

These are statement-fidelity and counterexample checks by the implementing
assistant, **not** separate independent mathematical referees.

## Executed finite adversarial variations

The pre-existing `scripts/check_banana_coherent_choices.py` was run in
the local Python 3.13 runtime. It passed every identity, inverse, extension
and composition test for all 17 bilinear matrices with l+r <= 3:
135 subpairs, 81 classes, 491 representative automorphisms,
1,277 partial isomorphisms and 82,697 composable pairs.

A new wrapper `scripts/check_banana_coherent_choice_variants.py`
reverses the enumeration order of:
- actual left/right subspaces,
- all source-to-target linear isomorphisms, and
- all ambient general-linear automorphisms.

This changes representative selection, representative identifications
and ambient conjugators, but retains one fixed choice per class/object.
The resulting independently *chosen* assignment again passed
all 82,697 composition tests, identities and inverse restrictions. The
result was the same under Python `-O`, because the existing coherent
choice runner raises explicit errors rather than using disabled asserts.

As a negative mutation, we replaced the classwise representative policy
with 'the latest isomorphic preceding object' for each object. The test
correctly failed with `isomorphic subpairs received different
representatives`. This is a deliberate invalid policy: it highlights
a necessary class-constancy assumption, not a mathematical counterexample
to coherent EPPA. Replacing it with 'the greatest element of the full
isomorphism class' passed every test again.

None of these computations checks Lean elaboration, uses a Lean kernel,
or supplies an independent referee.

## Exact-head local validation

The feature branch now inherits the hardened scripts on main. The driver
`scripts/verify_track_d_locally.sh` checks the Git SHA, clean working
tree, finite regression suite (including choice variants), explicit
negative guard probes, targeted new Lean axiom-audit module,
`lake build BANANA` and the global transitive-axiom audit.

Use the pinned toolchain from `lean-toolchain` and locally cached
dependencies, never GitHub Actions:

    EXPECTED_HEAD_SHA=<full-40-hex-PR-310-head> bash scripts/verify_track_d_locally.sh

This environment has no `lean`, `lake` or `elan` binary, and direct
GitHub DNS is unavailable. Thus the exact-head kernel gate has NOT run.
Only `propext`, `Classical.choice` and `Quot.sound` should occur
in successful transitive-axiom results. Independent mathematical
statement and counterexample reviews remain mandatory before merging
or marking the circulation theorem verified.


## Higher-dimensional mixed-sort regression (7 November 2026)

A new independent regression `scripts/check_banana_coherent_choices_dimension4.py`
reuses the already tested finite-choice implementation but selects precisely
the three dimension pairs `(4,1)`, `(4,2)`, `(4,3)` in the notation
`(total dimension, left dimension)`. Thus it enumerates ALL binary
pairings with left/right dimensions `(1,3)`, `(2,2)` and `(3,1)`,
including degenerate, rank-one, and nondegenerate matrices where possible.

The old runner was refactored only to accept an optional set of dimension
pairs; calling `run()` without arguments still runs the original 17 cases
in total dimension at most three, with identical result counts.
The expanded checks were executed in both ordinary Python and Python `-O`.
They contain **no disabled assertions**: the runner calls an unconditional
`check` function, and the wrapper checks all expected counts explicitly.

Recorded results, all passed:

| Test quantity | Count |
| --- | ---: |
| Pairing matrices (all mixed-sort matrices in dimension four) | 32 |
| Actual subpairs | 912 |
| Isomorphism classes | 333 |
| Representative automorphisms | 4,217 |
| Partial isomorphisms / inverse checks | 12,908 |
| Identity checks | 912 |
| Composable pairs, checked on both sorts | 770,480 |

These 32 matrices cover *mixed-sort* dimension four, not the one-sided
pairs `(4,0)` and `(0,4)`. Those one-sided pairings have very large
automorphism groups; no exhaustive claim is made for them here.
The 17 earlier small matrices include one-sided and zero-dimensional cases.

No new Lean module was edited for this larger finite test, and it does
not address the unavailable kernel verification. The results are
additional adversarial evidence only.


## Extended choice-policy regression in mixed dimension four

On 7 November the same reversal of subspace, isomorphism and ambient
automorphism enumeration was applied to the **entire mixed-sort
dimension-four collection**, not only the 17 smaller pairings.
Rather than adding a second large test implementation, the existing
`scripts/check_banana_coherent_choice_variants.py` now accepts
`--mixed4` to reuse the same exact finite groupoid validator
with the reversed fixed choices. Its default small-case interface
is unchanged.

Executed locally in ordinary and optimised Python 3.13:
- `python3 scripts/check_banana_coherent_choice_variants.py`
- `python3 -O scripts/check_banana_coherent_choice_variants.py`
- `python3 scripts/check_banana_coherent_choice_variants.py --mixed4`
- `python3 -O scripts/check_banana_coherent_choice_variants.py --mixed4`

Every invocation passed, with explicit checks active. In the
dimension-four variant: 32 pairing matrices, 912 actual subpairs,
333 isomorphism classes, 4,217 representative automorphisms,
12,908 partial isomorphisms and inverse checks, and 770,480
composable pairs checked on BOTH sorts. The test asserts the
complete expected count record, so an early-exit or omitted class
cannot silently produce a passing result.

This tests **robustness of the coherent construction under two
different fixed-choice policies**, not equality of the resulting
extension functions. Both policies can yield different automorphisms
for an individual arrow. One-sided dimension-four classes remain
outside this exhaustive regression; smaller tests include them.

The verification driver now runs this extended choice-policy test in
both Python modes. There is still no Lean compiler in the present
execution environment, and neither proof kernel verification nor
independent adversarial referee approval has occurred. Do not merge
or add circulation verification markers.

The literal expected SHA must be copied from the actual GitHub PR head.
Never set it to `git rev-parse HEAD` inside the checkout: that comparison
would be tautological. The verification driver now refuses missing or
malformed expected revisions, in addition to rejecting stale heads.
