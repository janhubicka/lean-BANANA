# Track C: directed finite stages and genuine global orbit quotients
## 7 November 2026 — internal adversarial handover

**DRAFT SOURCE ONLY.** The circulation manuscript and appendix are frozen.
This handover does not certify Lean elaboration or independent referee review.

### Mathematical advance

A finite Folkman limit should be assembled as a directed union of
finite two-sorted structures, with genuine embeddings of the finite
powerset rings into the ambient **non-unital** rings. The limit may
have no multiplicative identity. Accordingly the new
`FolkmanFiniteAtomStage` requires only `NonUnitalRing` on the
ambient sorts.

Each finite stage contains:
- a finite `FolkmanAtomStructure` code;
- an injective non-unital ring homomorphism from each atom-powerset
  ring into its ambient sort;
- the original cross-sort pairing reconstructed by the finite
  matrix for **all** source elements, not only named generators.

Each stage-refinement is a `FolkmanAtomEmbedding` whose partial
owner maps commute with both embeddings into the original ambient
structure for every finite atom subset. The source-fibre nonemptiness
is part of the genuine embedding data; target atoms may have no owner.

`FolkmanFiniteTupleStageWitness` records a finite-stage
representation of an actual labelled ambient tuple. A
`FolkmanDirectedFiniteStageAtlas` is supplied with two explicit
hypotheses: every finite labelled pair of tuples has a stage witness,
and any two witnesses of the same tuple have a common finite stage
refinement. These are **requirements**, not conclusions about an
unconstructed Fraïssé limit.

`folkmanFiniteTupleProfile_eq_of_commonStage` proves that profiles
computed in two different finite stages agree. The proof compares
the two tuples in a common stage using injectivity and the commuting
squares, then applies full profile invariance under the two atom
embeddings. `FolkmanDirectedFiniteStageAtlas.tupleProfile` uses
Classical.choice to select any stage, and
`tupleProfile_eq_witness` proves that this choice does not affect
the result. This includes zero-ring sorts, empty tuples and
unowned target atoms.

### Global automorphism endpoint

`FolkmanDirectedFiniteOrbitBridge.lean` combines stage-independent
profiles, the previously constructed finite generated two-sort
isomorphisms, and the generic finite-invariant quotient argument.
It has separate statements for ordered pairs of sort-specific
tuples and arbitrary mixed-sort tuples. Its orbit extension premise
remains explicit; the group action is not presumed to be the
genuine Folkman automorphism group.

The stronger
`FolkmanGlobalPairAutomorphismOrbits.lean` and
`FolkmanGlobalTaggedAutomorphismOrbits.lean` define the actual
orbit equivalence using pairs of non-unital ring equivalences
preserving the F2 cross-pairing on **every** ambient element.
Reflexivity, symmetry and transitivity are supplied by identity,
inverse and composition of these global automorphisms. Conditional
finiteness of the genuine orbit quotients follows from the
stage-independent finite invariant and the following *unremoved*
hypothesis:

> Every generator-preserving, pairing-preserving isomorphism between
> the finite generated structures arising from the stage witnesses
> extends to a genuine global pairing automorphism.

This is precisely the model-theoretic ultrahomogeneity/extension
task still to be proved about the countable Folkman limit.

### Independent-method finite adversarial regression

A Python checker in the current container uses
`frozenset`-valued ring elements, sets of incident atom pairs,
Option-valued partial atom owners and explicit two-step owner
composition. It is independent of the repository's original
bit-mask regression implementation, but it is **not** an
independently spawned proof referee and does not execute Lean.

It passed:
- 774 randomly sampled two-step finite stage configurations;
- 3,870 three-stage complete-profile comparisons;
- 30,506 cross-sort pairing identities;
- 91,710 ring-operation preservation identities;
- 513 configurations with a zero source sort;
- an explicit failure of unconditional orbit completeness in a
  finite non-homogeneous ambient Boolean ring;
- an optimised Python mode fail-closed check (exit code 1).

The counterexample is worth retaining: in the three-atom Boolean
ring with zero cross-pairing, the elements `{0}` and `{0,1}`
have the same one-generator **non-unital** profile (one realised
nonzero signature). They generate isomorphic one-atom rings.
However no automorphism of the full finite Boolean ring carries
one to the other: automorphisms preserve atom support cardinality.
This shows why profile completeness for *finite generated
substructures* must not be misreported as completeness for
*ambient global automorphism orbits* without homogeneity.

The local test source is
`/mnt/data/folkman_directed_stage_adversary_20261107.py`;
its execution log is in the same directory. It has not been
committed to the GitHub PR in this batch; the exact downloaded
script can be added after validation if useful.

### Mechanical source audit (NOT compilation)

The four new production Lean modules plus four dedicated
`#print axioms` modules are imported via
`FolkmanTupleTermPairIsoAxiomAudit.lean`, which is already
imported by `BANANA.lean`. The GitHub tree contained every
local import in these modules. Static inspection found no new
`sorry`, `admit`, `opaque` or `axiom` declaration in the
eight files. The audits request five, seven, six and six axiom
reports, respectively (24 in total).

No Lean, Lake or Elan executable is present in this runtime,
and local DNS cannot resolve github.com. GitHub Actions runners
are out of budget and were not invoked. Therefore **no pinned
Lean build, syntax/elaboration check, independent axiom report or
independent referee certification has been obtained**.

### Dependencies and next implementation steps

1. **Exact-head kernel gate:** on a trusted local checkout run
   `python3 scripts/check_lean_module_graph.py`, then
   `lake build BANANA` and
   `bash scripts/audit_all_axioms_local.sh`. Resolve any Lean
   elaboration failures before advancing a manuscript marker.
2. **Track B/native class:** PR #309 now contains the requested
   exact finite-index morphism witness, but remains dependent on
   unverified PR #305; the finite native hereditary construction
   also needs its own kernel verification and intrinsic-unit audit.
3. **Construct the limit:** produce a countable exhaustive chain
   (or a directed finite-stage system) satisfying the coverage and
   common-refinement fields, with the ambient original non-unital
   operations and cross-pairing.
4. **Prove actual ultrahomogeneity:** isomorphisms between the
   *finitely generated non-unital* two-sort substructures must
   extend to global pairing-preserving automorphisms. This is
   the sole missing premise of the new genuine orbit bounds.
5. **Finish omega-categoricity:** the mixed-sort global
   automorphism orbit quotient would then be finite for each n.
   Ryll–Nardzewski can remain an explicitly cited external
   standard consequence, as in the existing project conventions.
6. **Independent referees:** obtain independent adversarial proof
   reviews of the full finite profile theorem, the stage atlas,
   the intrinsic-unit/heredity interface and global extension.
   Neither static audits nor Python regressions satisfy this gate.

**Do not merge draft PR #308 or add circulation validation markers
without the kernel and independent-referee checks.**
