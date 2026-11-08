# BANANA Track D — adversarial groupoid audit, 6 November 2026

Internal development note. This is **not** circulation prose, a Lean kernel
check, or a report by an independently spawned mathematical referee.
No TeX source, existing validation markers, or TODO commands are changed.

## 1. Paper-level theorem versus staged Lean

The circulation statement says that each finite BANANA pairing
(A=(L_A,R_A,\beta)) has a coherent EPPA witness with *both* sides of
dimension (\dim L_A+\dim R_A). The staged
`exists_bananaActualCoherentEPPA` is stronger in precision but not in
assumptions: it names a single map `Theta` from **all** actual
pairing-preserving partial automorphisms, represented as isomorphisms
between pairs of vector subspaces of (A), to automorphisms of its
standard perfect completion (B_{\ell+r}). It requires identities and
inverses to be preserved and
`Theta(q) * Theta(p) = Theta(p.trans q)` for composable arrows.
It states the restriction equality separately on both sorts. There
is no nondegeneracy or positivity assumption on either dimension.

The signature is an *uncompiled source declaration*, not a kernel-checked
theorem. The manuscript must not acquire a full validation marker
until this declaration and all dependencies elaborate and pass the
transitive-axiom audit.

## 2. Independent mathematical derivation of the construction

Let (n=\dim L_A+\dim R_A). Embed (A) into the standard perfect
pairing (B_n) by the canonical perfect completion. Groupoid objects
are actual pairs of subspaces (U=(U_L,U_R)\subseteq A); arrows are
two-sided linear isomorphisms preserving their restricted pairings.

For each isomorphism class (i) of those objects, choose ONE
representative (U_i). Its completion is a perfect pair of side
dimension (m_i=\dim U_{i,L}+\dim U_{i,R}\le n). Align an embedding
of this completion with the given inclusion of (U_i) into (B_n).
The canonical completion action
(f\oplus(g^{-1})^*) and its contragredient right action, extended
identically over the orthogonal complement, give a homomorphism
(\rho_i:\operatorname{Aut}(U_i)\to\operatorname{Aut}(B_n)) which restricts
to the prescribed automorphisms on both sorts.

For each actual object (U) of class (i), choose ONE fixed
isomorphism (iota_U:U_i\to U) and ONE ambient automorphism
(h_U\in\operatorname{Aut}(B_n)) whose restrictions are (iota_U)
on the two original sorts. Existence of such a **single** (h_U)
simultaneously for both sorts follows from perfect-pair
homogeneity, not from two independently chosen linear extensions.

For every arrow (p:U\to V) in class (i), put

    Theta(p) = h_V rho_i(iota_V^{-1} p iota_U) h_U^{-1}.

The middle term lies in the **actual pairing-preserving**
automorphism group of (U_i). If (p) is the identity at (U),
the middle term is the identity; therefore Theta(p)=1.
For composable (p:U\to V) and (q:V\to W),
the adjacent terms (h_V^{-1}h_V) cancel and the homomorphism
property of (\rho_i) gives
`Theta(q) * Theta(p) = Theta(q p)`. Inversion follows.
For (x\in U), move backwards by (h_U^{-1}), apply the middle
automorphism via (\rho_i), and then move forwards by (h_V):
the result is (p(x)) in the corresponding embedded sort.
The argument applies separately to left and right. Different
isomorphism classes cannot contain the endpoints of a single arrow,
so choosing this construction independently for each class creates
no additional composability requirement.

This is an elementary algebraic cross-check; it was not obtained
by a second independent model call and must not be confused with a
second formal verification.

## 3. Exact source-level checks at PR #310

The GitHub tree and PR patch were inspected at the current Track D
head, after the runtime-guard repair. There are **24 added Lean files**,
of which the production files are reached by the added axiom-audit
imports. All **35** local `BANANA.*` import references in those
files have matching repository paths. The **73** printed axiom-query
declarations resolve by name: 69 in new files, four to previously
existing `CoherentConjugation` and `CoherentEppaPackage` theorems.
No production module added by the PR is omitted from this static
audit-import reachability check. This DOES NOT check Lean
elaboration or the actual transitive axiom sets.

The PR remains draft. GitHub runners are out of budget. This runtime
contains neither `lean` nor `lake`, and direct GitHub DNS access
from the execution container fails.

## 4. Adversarial corner cases and possible proof gaps

* **Zero left/right sorts:** a zero-dimensional vector-space sort
  contains its zero, not an empty carrier. All constructions use
  pairing-preserving linear maps and should accommodate this.
* **Degenerate restricted pairings:** representatives may be
  degenerate; only their perfect completions and the ambient witness
  are required to be nondegenerate.
* **Wrong multiplication order:** the correct order is
  `Theta(q) * Theta(p)`, not `Theta(p) * Theta(q)`; the
  previous finite mutation tests reject reversal.
* **Fresh coordinate selection per arrow:** it can destroy
  composition; fixed presentations for each object are essential.
  The new actual-subpair functor models precisely this requirement.
* **Dependent quotient casts:** the source class is fixed for an arrow
  and the equality witnessing the target's membership is a proof.
  The proposed descent uses proof irrelevance and an explicit
  change-index lemma. This is the highest-priority Lean
  elaboration/statement-fidelity check.
* **Self-embeddings of finite perfect blocks:** converting an
  injective self-map into an equivalence relies on the domain and
  codomain being the same finite carrier. It must not be generalised
  to embeddings between different objects.
* **One common witness:** all classes use exactly (B_n);
  choosing a separate completion for each arrow would not prove
  coherent EPPA.

A separate sharpness observation is mathematical, not merely
experimental: for the zero pairing on dimensions ((\ell,r)), any
pair-preserving embedding into (B_n) has images (U,V) with
(V\subseteq U^{\perp}). Therefore
(r=\dim V\le n-\dim U=n-\ell), so (n\ge\ell+r).
The completion construction attains this bound.

## 5. Corrected finite regression and audit gate

The ORIGINAL `scripts/check_banana_actual_coordinate_functor.py`
contained eight Python `assert` statements. Under `python -O`
they vanished, so the earlier matching optimised output was
**not** independent evidence of validated identities.
In commit `bfcb1a84646e239c7aa87d3f114aaae4152c3b84`, all guards
were replaced by unconditional `check` calls. Both normal and
optimised runs now genuinely test all **1,277** arrows and
**82,697** composable pairs across 17 small pairing matrices.
A deliberately false `--probe-guard` produces a nonzero exit
with `AssertionError: CHECK_GUARD_ACTIVE` in both modes.
The other Track D finite scripts containing `assert` should be
run without Python optimisation unless similarly repaired.

At the exact PR head, on a local checkout with the pinned Lean toolchain:

    python3 scripts/check_lean_module_graph.py
    lake env lean BANANA/NonPrecompact/BananaActualSubpairUnindexedCoherenceAxiomAudit.lean
    lake build BANANA
    bash scripts/audit_all_axioms_local.sh
    python3 scripts/check_banana_actual_coordinate_functor.py
    python3 -O scripts/check_banana_actual_coordinate_functor.py
    python3 scripts/check_banana_actual_coordinate_functor.py --probe-guard
    python3 -O scripts/check_banana_actual_coordinate_functor.py --probe-guard

The final two commands **must fail**, by design.
Inspect all transitive axioms and allow only `propext`,
`Classical.choice` and `Quot.sound`. Do not merge
or add a full theorem validation marker before those checks
and actual independent referee reviews have succeeded.


## 6. Verification scripts synchronised with main

The PR branch is 37 commits behind main in Git history; the intervening
mainline changes were inspected and do not alter the mathematical
dependencies used by Track D. They do, however, upgrade the *local
verification machinery*. On this branch the following five files were
copied byte-for-byte from main commit
`ba5eb4de92bef50708cd226fcda6b2c01baf8051`:

- `scripts/check_axiom_report.py`
- `scripts/audit_all_axioms_local.sh`
- `scripts/check_lean_module_graph.py`
- `scripts/test_check_axiom_report.py`
- `scripts/test_check_lean_module_graph.py`

The hardened versions strip Lean comments before parsing commands,
reject missing or unexpected axiom reports and distinguish production
modules imported only by axiom-audit entry points from genuinely dead
modules. No mathematical Lean source was altered by this synchronisation.

A new local-only `scripts/verify_track_d_locally.sh` runs both verifier
self-test suites, the full finite regression suite, the positive and
negative optimised-mode tests, and (where Lake is installed) the
targeted module build, root build and transitive-axiom audit. It checks
a clean Git tree and optionally enforces `EXPECTED_HEAD_SHA`.
The Bash source passed `bash -n` locally, but the full driver cannot
be executed in this environment without Lean, Lake and a checkout of
the pinned dependencies. It does not start GitHub Actions.

Before final integration, bring the PR onto a current mainline commit,
rerun the exact-head driver and repeat the independent mathematical
proof review. No PR merge or manuscript validation marker is justified
by these source checks alone.


## 7. Source dependency audit (7 November 2026)

The direct import closure of the proposed final declaration
`exists_bananaActualCoherentEPPA` was recomputed from the pull-request
diff, not inferred from broad module counts. The final theorem depends
on **13** new Track D production modules, including the quotient atlas,
the actual-subpair coordinate functor, the aligned action, and the
groupoid descent.

Two additional Track D production modules are **audit-only auxiliaries**:
`BananaMatrixCompletionActionHom.lean` packages the unembedded
completion action as a homomorphism, and
`CoherentEppaRepresentativeTransport.lean` supplies a generic
MulAction transport calculation. They are imported by axiom-audit
entry points but are not transitive inputs to the final theorem.
This is not by itself evidence that either file is incorrect or dead:
the first is a reusable standalone result, and the second is a
general group-action abstraction. Any later cleanup decision must
consider their reusable purpose and fully compiled dependent checks,
not merely their absence from the final theorem's import closure.

The prior static PR audit found all local import paths and printed
axiom names resolvable. The current GitHub mainline merge remains
clean. This is still a source-level review, not a Lean kernel audit.


## 8. Exact-head gate repair and independently executed orchestration test (7 November)

The earlier `verify_track_d_locally.sh` built only the final
`BananaActualSubpairUnindexedCoherenceAxiomAudit` target. That target
reaches 13 new production modules, but it does **not** import two
standalone auxiliary modules. A successful build of only that target
would not certify those auxiliaries. This is a genuine verification
coverage gap, not a counterexample to coherent EPPA.

The local gate now explicitly runs `lake build +Module` and
`lake env lean` for **all nine** Track D `AxiomAudit.lean` modules
and checks each resulting report with the repository's strict
`scripts/check_axiom_report.py`. The list was compared with the
current PR diff: nine present, nine listed, no omissions or extras.
The module-target notation is documented by the official Lean/Lake
manual; it has not been executed here against the actual pinned toolchain.

A new `scripts/test_verify_track_d_driver.py` exercises the exact
driver in a disposable clean Git checkout, using a fake `lake` binary
and mock axiom outputs. This executable test was run locally with
Python 3.13.5; it verified:
- the Bash driver passes syntax checking;
- all nine audit modules are individually built and interrogated,
  and exactly one root build and one global audit are invoked;
- both normal and optimised negative regression guards are exercised;
- an incorrect `EXPECTED_HEAD_SHA` is rejected;
- no GitHub Actions are used.

The local test file is byte-identical to GitHub blob
`63afb6c52ca069beafafa6acb09fc94ce9672fa9`.
The final driver, including this test, is byte-identical to GitHub blob
`20d26566cf72f3c6f205c2578d035792b48ed8f3`.
This was independently checked using `git hash-object` in the
execution container. The original finite regression script and
alternative-choice script were also verified against their exact
GitHub blobs and rerun.

**Boundary:** the mocked Lake test proves only orchestration and
failure signalling. No real Lean/Lake executable or compiled Mathlib
dependencies are present, and no kernel elaboration, transitive-axiom
inspection, or independent mathematical referee sign-off has occurred.
The 9-module gate must be rerun on the exact PR head in a real pinned
Lean environment, and the full end-to-end theorem must compile there
before any validation marker or merge.

## 9. Required external PR-head identity (8 November)

The verification driver previously allowed no `EXPECTED_HEAD_SHA`,
which could certify an unintended checkout. This is now a hard failure:
`EXPECTED_HEAD_SHA` must be provided as a 40-character lowercase SHA
copied from the GitHub PR head. A missing, malformed, or different SHA
is rejected before any tests execute. The fake-Lake unit test was
extended to cover all three negative cases.

**Do not** use `EXPECTED_HEAD_SHA=$(git rev-parse HEAD)` for this purpose:
it only compares the checkout to itself. The exact PR head is a
separate externally obtained reference. This correction affects only
the local verification gate, not any mathematical theorem or TeX.


## 10. Legacy finite-group regression and optimisation guard (8 November)

A separate adversarial audit re-executed the **exact committed script**
`scripts/check_banana_finite_aut_completion_group.py` in local
ordinary Python (not `-O`). The local script's Git blob was
`68d5b0d3c8482d590d911ae849760203cb785a5c`, identical to
the blob in PR #310. It enumerated all 17 binary bilinear forms of
total dimension at most three, all 377 pairing-preserving
two-sorted linear automorphisms, and all **56,621** ordered
automorphism products. Every original-source assertion passed,
including subgroup closure, identity and inverses, preservation
of the perfect pairing, restrictions to both original sorts and
composition of the canonical completion action. This is a
computer experiment, not a proof in Lean or an independent
mathematical referee.

**Newly identified verification hazard:** this and several other older
finite scripts use Python `assert`. A shell environment with
`PYTHONOPTIMIZE=1` causes even `python3 script.py` to disable
all their assertions silently. The exact-head shell driver
now fails at the start if the ordinary `python3` executable
reports a nonzero `sys.flags.optimize`. Explicit `python3 -O`
tests are kept for scripts that use unconditional runtime checks.
The local guard's positive and negative outcomes were reproduced.
The fake-Lake unit test was extended to assert that a
`PYTHONOPTIMIZE=1` subprocess fails with the intended diagnostic.

This repair does not eliminate the need for Lean compilation or
transitive-axiom inspection. It is solely a correction to the
preflight evidence: `-O` outputs from older `assert`-based
tests must never count towards validated theorem coverage.

## 11. Pinned API and current-main compatibility (8 November)

The pinned toolchain is leanprover/lean4:v4.35.0-rc3. The successor-tree
dependency pins Mathlib to commit
5bd58ac291422a21f412ae354c91e7d172255a2c,
which is the relevant source revision, not Mathlib's current master.

A fresh audit of the pinned Mathlib sources confirmed the following
exact interfaces used in Track D:

- Mathlib/Algebra/Module/Equiv/Basic.lean defines
  LinearEquiv.mul_eq_trans as f * g = g.trans f, and
  LinearEquiv.mul_apply as (f * g) x = f (g x).
  Therefore the groupoid code's multiplication direction agrees
  with the finite automorphism subgroup's convention.
- Mathlib/LinearAlgebra/Dimension/Finrank.lean includes
  LinearEquiv.finrank_eq, the dimension-of-image step.
- Mathlib/Data/Fintype/Card.lean provides
  Finite.injective_iff_surjective, applicable to a self-map
  of a finite type, not to an arbitrary embedding between
  different types.
- The merged BananaFiniteFraisseProperties.lean proves
  BananaMatrixStructure.exists_substructure_with_ranges.
  The Track D actual-subpair atlas reuses this theorem;
  it does not postulate its own hereditary axiom.

These checks eliminate a suspected *missing API name* problem, but
they do NOT typecheck any new Lean declaration. In particular, the
dependent quotient transports, nested Subtype inference and
change/rfl steps remain unverified. No mathematical missing hypothesis
was found in this targeted API audit.

Merge commit 7de43645a08ac2b73ba1ddcbfa703587201325f1
incorporates main at 97660c8d0824ef58739e9e42768ce98b164b81c4
into the draft. All 45 Track-D-only blobs and every mainline blob
were checked byte-for-byte before the ref update. The one
main-only overlapping root-file change (BANANA.lean) is taken
from main. The resulting PR diff has only added files, no TeX.

There is still no Lean/Lake/Elan executable or cached compiler in
the execution container, and direct GitHub access fails DNS.
GitHub runners are out of budget. Thus this continuation provides
no kernel compilation or printed transitive-axiom report.
No independent adversarial mathematical referee has signed off.
Do not merge Track D or add a circulation validation marker yet.

## 12. Clean-checkout repeatability (8 November)

Another executable preflight defect was identified and reproduced in a
fresh local Git repository: importing the finite coherent-choice
Python module creates an untracked __pycache__/ directory when the
repository has no ignore rules. The verification driver previously
checked a clean tree only BEFORE running the test suite. The second
invocation could therefore fail its exact-head cleanliness test,
despite the first invocation succeeding and without any source edit.

The branch originally had no .gitignore. Its new minimal .gitignore
ignores only local build products (.lake/) and generated Python
bytecode (__pycache__/ and *.py[cod]). The driver additionally
exports PYTHONDONTWRITEBYTECODE=1 before invoking any test scripts.
Both controls are necessary in practice: ordinary Python imports
can create caches, while real Lake builds create .lake/ objects.

A separate temp-repository check was executed locally: generated
.lake/build/Mock.olean and Python cache files were ignored, the
suppressed-bytecode import left no untracked files, and two
consecutive dry-run checks had clean Git status. This tests
Git/bytecode behaviour, not Lean.

The staged fake-Lake driver regression was also extended to
copy the exact .gitignore into its mock checkout, exercise a
real sibling-module Python import, simulate .lake/build/Mock.olean,
assert no bytecode cache is emitted and the Git tree remains clean,
and run the full mocked verification driver TWICE on the same
revision. The extended mock test still needs to be executed on
the exact committed source with a local checkout; do not report
it as a passed real Lean build.

The latest mainline Folkman-only changes were merged into the
draft at commit eba7b1a429cfc9ee63bdbd3e2efa6d0c096f628b.
No Track D theorem files, circulation TeX, original TODO notes,
or validation markers were modified. PR #310 remains draft.
