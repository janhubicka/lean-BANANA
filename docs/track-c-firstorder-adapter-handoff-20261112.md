# BANANA Track C — faithful first-order adapter handover
12 November 2026 — internal only, NOT kernel-verified

## Scope and change control

The circulation part of the BANANA paper remains frozen.
Only Lean source, local semantic tests, axiom-query modules and
this internal note were changed. No TeX, bibliography, appendix,
manuscript TODO or validation marker was changed or reinstated.
The draft PR #308 remains unmerged.

## Exact first-order encoding

Let L and R be the original non-unital Boolean-ring sorts, with
F₂-valued cross-pairing β. Use the tagged disjoint carrier Sum L R.
The single-sorted first-order language has:

* two distinct named constants, the left and right zeros;
* four binary function symbols, left addition, left product,
  right addition, right product;
* two unary predicates marking the left and right sorts;
* one binary relation recording β(x,y)=1 for left x, right y,
  and false on all wrong-sort arguments.

An operation applied to a wrong-sort argument returns zero in its
OWN output sort. This makes the operations total. There is
NO named multiplicative identity, and no unary negative operation.
In a Boolean ring additive inversion is already the identity;
for general non-unital rings the substructure converse would
need an additional assumption (e.g. characteristic two), which
the directed Folkman atlas supplies separately.

A native embedding fL,fR preserving zero, addition, multiplication
and every β-value produces a one-sorted first-order embedding
through Sum.map. Its injectivity follows from injectivity on
both sorts. Sort predicates and the pairing-one relation are
reflected, not merely preserved.

Conversely, a tagged first-order embedding must preserve both
sort predicates and therefore restrict to separate maps on L
and R. Preservation of the two zero constants, four functions
and injectivity yields two injective non-unital ring homomorphisms.
Reflection of the pairing-one predicate is equivalent to equality
of all β-values, since F₂ has only 0 and 1. In particular,
the reverse adapter must use reflection of the relation; merely
preserving the implication would NOT be enough.

For finite Boolean-ring carriers, every first-order substructure
is the tagged union of two non-unital subrings, and vice versa.
The generated first-order substructure of tagged finite tuples is
EXACTLY the tagged union of their two native generated subrings.
This includes empty tuples: their generated first-order
substructure contains two distinct zero constants.
The intrinsic units of the two finite subrings need not equal
the ambient units and are not named in this language.

## Source modules

Track C currently has the following NEW source-only adapter
modules on its draft branch:

1. FolkmanFirstOrderSignature.lean — finite symbol inventory
   and countability;
2. FolkmanFirstOrderInterpretation.lean — original operations,
   tags and pairing interpreted on Sum L R;
3. FolkmanFirstOrderNativeEmbedding.lean — native embedding
   to first-order embedding;
4. FolkmanFirstOrderEmbeddingConverse.lean — first-order
   embedding to genuine original non-unital pairing embedding;
5. FolkmanFirstOrderSubstructure.lean — native subring pair
   to first-order substructure;
6. FolkmanFirstOrderSubstructureConverse.lean — reverse
   substructure recovery for Boolean-ring carriers;
7. FolkmanFirstOrderGeneratedClosure.lean — exact generated
   closure equality;
8. FolkmanFirstOrderRepresentatives.lean — actual finite
   tagged representative for each Folkman atom-matrix code,
   with finite/countable carriers and finite generation.

There are eight dedicated axiom-query modules for these.
A complete Git tree/source audit found all imports, no new
sorry/admit/axiom/opaque declarations, and all 44 production
declarations covered by exact #print axioms queries.
The audit files are reachable from the existing BANANA.lean
root. The local exact-head script lists the eight production
modules in dependency order and the three finite encoding
regressions. This is STRUCTURAL review, not Lean elaboration
or an executed transitive axiom audit.

## Independent-method finite semantic tests

1. Native-to-tagged encoding, run locally before this increment:
   1,296 finite native morphisms, 34,496 relation comparisons,
   3,888 generated-substructure comparisons, including zero
   ring sorts, empty tuples and unused target atoms.
2. Converse finite embedding test:
   all 29 injective tiny Boolean-ring homomorphisms were
   precisely the corresponding partial atom-owner maps;
   341 pairing diagrams and 991 pairing comparisons.
3. Tagged substructures and generated closures, run locally
   on 12 November:
   2,209 candidate tagged subsets, 529 genuine substructures
   recognised, 10,816 generated-closure comparisons,
   16 empty-tuple cases and 615 zero-sort cases.

All semantic tests passed and refuse Python -O.
These are NOT Lean proofs, not transitive axiom reports,
and not separately spawned adversarial referee agents.

## External classical Fraïssé existence theorem

Cameron Freer's Apache-2.0-licensed computable-model-theory
project at exact historical commit
a1fe76155a98f03933f7de0811e03b2473dd2e21
uses Lean 4.35.0-rc3, the same toolchain as BANANA.
Its external exact-head CI run 37225534306 succeeded.
The reusable Mathlib-only classical layer includes:

- RepresentativeAge.lean
- ExtensionRichFamily.lean
- ExtensionRichDirectLimit.lean
- FraisseExistence.lean

The main theorem
FirstOrder.Language.exists_isFraisseLimit_representativeClass
constructs a countable Fraïssé limit from countable finite
representatives, hereditary closure, joint embedding and AP.
It serves HISTORICAL embedding requirements as well as the
current stage. The source modules are byte-identical to their
later Lean 4.36 counterpart. The historical external package
nevertheless uses a different Mathlib fork, so it cannot
yet be claimed compatible with BANANA's pinned official
Mathlib revision.

Do not change BANANA's Lean/Mathlib pins merely to import
this project. If the four classical modules are ported,
preserve their Apache-2.0 attribution, isolate the port on
a separate reviewable branch, and compile it against the
exact BANANA pin before using it as a dependency.
No such kernel-verified port has yet been made.

## Remaining substantive proof and verification tasks

1. **Formal finite-class transfer.**
   Define F(A) as the tagged first-order structure representing
   each finite Folkman atom code A. The merged native Track B
   finite-class certificate supplies original-language
   heredity, JEP and strong AP; transfer the actual
   commuting embedding squares through the two directions
   of the adapter above. Heredity specifically needs the
   generated-substructure equivalence and intrinsic finite
   subring identities. Do not infer a native amalgamation
   solely from an abstract atom-matrix code.
2. **Port/reuse classical existence.**
   Kernel-check the external classical Fraïssé existence
   theorem on BANANA's pinned official Mathlib or implement
   an equivalent native direct-limit construction with
   fair historical-stage scheduling. Then instantiate it
   using the tagged finite representative class F.
3. **Extract the countable original-language limit.**
   The limit must have exactly two sorts partitioning its
   underlying carrier, each containing its named zero.
   Recover non-unital Boolean-ring operations and the
   original F₂ pairing from the first-order interpretation.
   Show finite tagged age/coverage implies all universal
   Boolean-ring and pairing laws, a directed finite-stage
   atlas and the actual finite EPP.
4. **Close the already drafted Track C theorem.**
   Instantiate folkmanGlobalTupleRelated_iff_profile_eq_of_atlas_EPP
   and the mixed-sort orbit finiteness result in the
   constructed countable limit. Ryll–Nardzewski may remain
   an explicitly cited external standard theorem.
5. **Verification and adversarial referees.**
   Exact-head local Lean 4.35.0-rc3 build of PR #308,
   full transitive #print axioms results, and genuinely
   independent adversarial reviews must pass before merging
   or adding manuscript validation markers.

## Current blocker

The current container contains no lean, lake or elan and
cannot resolve github.com via DNS. Connected GitHub APIs
can read/write source but cannot furnish a pinned local
compiler. GitHub Actions are out of budget and were not run.
Therefore NO new source module is claimed kernel-verified.
No independent referee agent could be spawned with the
available tools. PR #308 MUST remain draft and unmerged.
