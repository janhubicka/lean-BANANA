# Track D — circulation statement versus Lean interface (8 November 2026)

INTERNAL REFEREE NOTE ONLY. Not circulation prose, a TeX patch,
an independently spawned referee report, or a kernel check.

## Source snapshot

* Frozen circulation source: private janhubicka/BANANA,
  `banana-eppa.tex`, main blob `829938eb1c56652d51f9baaede2ce36299624b72`
  at manuscript main commit `e2b441c528fc76e269f916bac324c7fee30b0298`.
* Exact theorem: `thm:eppa`, top of the BANANA coherent EPPA subsection.
  It states that every BANANA structure `A=(L_A,R_A,beta_A)` admits a
  coherent EPPA witness `B` with both side dimensions
  `dim L_B=dim R_B=dim L_A+dim R_A`.
* The manuscript already contains the TODO
  `Lean: class-wide coherent-EPPA bookkeeping remains open.`
  Do not remove or overwrite this TODO until exact-head Lean compilation
  and genuine independent adversarial reviews have succeeded.
  Do not restore any previous TODO that a human co-author has removed.

## Exact representation of the intended theorem in the staged Lean source

`exists_bananaActualCoherentEPPA` in
`BANANA/NonPrecompact/BananaActualSubpairUnindexedCoherence.lean`
quantifies over every original finite
`A : BananaMatrixStructure l r` and returns one function `Theta`
from **all** pairing-preserving partial isomorphisms of A to the
automorphism group of `perfectBanana (l+r)`.

* **Substructures:** `BananaActualSubpair A` consists of one
  left submodule and one right submodule. Since the original vector
  spaces are finite, every such submodule is a finite substructure
  of the language with vector-space operations and pairing relation.
* **Partial automorphisms:** `BananaActualSubpairIso U V` is a
  left and a right linear equivalence preserving the restricted
  F₂-valued pairing. In F₂, preservation and reflection of the
  incidence relation beta=1 is equivalent to equality of the pairing.
  This is also the content of the existing `edge_iff` API for
  `BananaMatrixEmbedding`; no unspoken nondegeneracy condition is used.
* **Witness:** the codomain is
  `BananaMatrixAutGroup (perfectBanana (l+r))`.
  This is the actual two-sorted pairing-preserving linear automorphism
  group, not two unrelated `GL` elements.
* **Fixed copy of A:** every restriction equation uses the SAME
  `A.completionEmbedding`. Both vector-space sorts are treated.
* **Coherence:** the statement requires
  `Theta(refl U)=1`,
  `Theta q * Theta p = Theta (p.trans q)` for every composable pair,
  and `(Theta p)⁻¹=Theta p.symm`. These equalities are strong enough
  for the coherent-triple convention used in structural Ramsey/EPPA.
* **No additional mathematical hypotheses:** no assumption that
  either side is nonzero, that beta is nondegenerate, that individual
  partial maps extend in advance, or that a representative
  identification/conjugator has been supplied by the caller.
  Internal `Classical.choice` merely fixes such data.

## Adversarial statement-fidelity risks

1. **Do not confuse individual EPPA with coherent EPPA.** Homogeneity
   of the perfect completion extends a single partial isomorphism.
   Coherence needs one group homomorphism on each representative and
   fixed conjugators for all objects in its class.
2. **Do not confuse two sorts with one.** An ambient left automorphism
   determines the right contragredient; arbitrary independent left
   and right maps need not preserve the pairing. The staged type uses
   the actual paired subgroup.
3. **Do not change the representative between composable arrows.**
   The cancellation of the middle conjugator and coordinate change
   must be literally the same object. The source uses a fixed
   presentation per actual subpair.
4. **Do not silently omit the zero-dimensional cases.** The zero
   vector space has one vector, not an empty carrier. Finite
   regressions include l=0 or r=0.
5. **Do not claim the answer is independent of classical choices.**
   Different coherent functions may arise from different
   representatives; existence, restriction and composition are
   the theorem's requirements.
6. **Do not treat the current Lean text as verified.** The final
   theorem and the 13 new transitive proof modules have not been
   elaborated by the pinned Lean compiler. `#print axioms` lines
   are staged queries, not executed evidence. An error in any
   submodule invalidates every downstream validation claim.

## Revised verification priority

The local driver `scripts/verify_track_d_locally.sh` has been
reordered in a verified dependency-respecting sequence. The first
three audit modules each introduce just one new independent
production module; later targets grow through two, five, eight,
nine, ten and finally thirteen new production dependencies.
This lets a real pinned build report the earliest failing module,
rather than attempting the whole end-to-end theorem first.

The nine modules still include both standalone auxiliary results
that do not occur in the final theorem's transitive closure.
The correct Lake module-target spelling `lake build +Module`
was separately checked against the official Lake reference.
A local fake-Lake orchestration test verifies the command sequence,
but cannot verify its Lean contents.

### Final completion gate

1. Check out the exact latest PR #310 head, with a clean working tree.
2. Run `EXPECTED_HEAD_SHA=<literal head SHA> bash scripts/verify_track_d_locally.sh`
   on a server that has the pinned toolchain/dependency cache.
   Do not use GitHub Actions. The literal expected SHA must be
   obtained from the PR and not simply set to the checkout's
   `git rev-parse HEAD` (which would be a tautological check).
3. Repair any elaboration failures in dependency order, rerunning
   the complete gate after each relevant fix.
4. Inspect every transitive axiom report; permit only Lean's standard
   `propext`, `Classical.choice` and `Quot.sound`.
5. Obtain genuinely independent adversarial referee reviews of the
   actual Lean statements and their mathematical fidelity to
   `thm:eppa`.
6. Only after successful kernel checks and independent review:
   request circulation-owner approval to replace the already
   existing class-wide TODO with a validation marker. The
   manuscript is frozen.

No changes to circulation text, manuscript TODOs, validation
markers, appendix or TeX infrastructure were made here.
