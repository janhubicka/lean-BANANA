# Track C finite-to-global reduction: atlas plus finite EPP
11 November 2026 — internal adversarial handover

**Status: new Lean source only; NOT kernel verified.**
The circulation part of the BANANA manuscript is frozen and was not
changed. No TODO removed by Sofia was reintroduced. GitHub Actions
were not dispatched.

## Exact conditional statement reached

Let M have two non-unital ring sorts L and R and an original
F₂-valued cross-sort pairing β. Suppose that:

1. L and R are countable;
2. M has a directed finite-stage atlas, with each stage an actual
   embedding of a finite Boolean-ring pairing into the original
   non-unital two-sorted language, covering every finite tuple and
   providing common refinements of two presentations of the same
   tuple;
3. M has finite EPP for finite atom-coded Folkman objects: an
   embedding of finite codes A→B and a faithful embedding A→M
   extend to a faithful embedding B→M preserving zero, both
   ring operations and the COMPLETE β pairing on every element.

Then finite generated-substructure isomorphisms of M extend to
actual global pairing-preserving automorphisms. True global
automorphism-orbit equivalence on every ordered two-sort tuple
pair, and every tagged mixed-sort tuple, is exactly equality of
their complete positive-pattern/pairing-matrix profile. The orbit
quotient is finite for each fixed pair/total tuple length.

The drafted Lean source proving this conditional result is:
- FolkmanFinitePairedBridgeSwap.lean
- FolkmanForthBridgeHomogeneity.lean
- FolkmanFiniteHullEPPBridge.lean
- FolkmanFiniteSourceHullsFromAtlas.lean
- FolkmanGlobalEPPCompletion.lean

Five dedicated exact #print axioms modules are included in the root
BANANA.lean audit chain. No global ambient ring unit is assumed.

## Independent mathematical checks (different approaches, not agents)

### Approach A: algebraic lift and a common finite stage

Take any finite paired bridge P, whose source code rings are
finite. Enumerate ALL elements of both code carriers, not only
the originally distinguished tuple. Adjoin one ambient element
x on either sort, forming a single finite tuple. The directed
atlas supplies a finite stage S containing it.

The source homomorphisms of P factor through S because their
whole finite images were explicitly enumerated. For every source
element a, choose an element i(a) of S with
S.map(i(a))=P.source(a). As S.map is injective,
this choice is UNIQUE. Zero/addition/multiplication of the
chosen representatives therefore commute with the source
homomorphism: proving the ring laws requires applying the
injective map S.map to both sides. We get genuine injective
non-unital ring homomorphisms i_L and i_R from the original
code into S. The exact β values on S show that i_L and i_R
preserve the complete finite atom matrix.

Apply the finite EPP to the other copy of P and the finite
code embedding i:P.code→S.code. It supplies a faithful second
embedding of S into the same ambient pairing. Both embeddings
give a larger finite paired bridge Q. The square commutes on
EVERY element of both old code rings; the requested new x lies
in Q's source image. Thus this proves source-left and
source-right one-point extension from the atlas and EPP.

### Approach B: source/target symmetry of paired diagrams

The finite bridge includes two injective copies of exactly the
same finite two-sort code, both with the same full atom matrix.
Exchanging them is an involution and sends every commuting
extension square to a commuting extension square. Consequently
a source-left extension of the SWAPPED bridge becomes the
target-left extension of the original bridge, and similarly
on the right. Only two forth conditions are mathematically
independent.

As in the established pre-BANANA back-and-forth proof, fair
cofinal enumeration of source/target × left/right requirements
then produces a monotone exhaustive coherent sequence of
finite paired bridges. The generic paired-bridge endpoint
assembles the resulting bijections of both entire non-unital
rings and proves the original pairing is preserved. An initial
bridge for each finite generated isomorphism was constructed
in the previous Track C increment using its own intrinsic
finite Boolean-ring identities and the merged Track B native
atom-code theorem. Thus generated homogeneity follows.

## Adversarial edge cases

- Empty generators produce zero rings with intrinsic unit zero,
  not an ambient unit.
- The target of a non-unital embedding may have unowned atoms:
  a finite stage hull must retain ALL elements of the old code
  and not merely its intrinsic identity.
- Injectivity is necessary for the unique ring-homomorphism
  factorisation. Without it, a choice of preimages need not
  respect either ring operation.
- Pairing preservation on named generators is weaker than
  preservation of the entire finite matrix; the finite
  extension hypothesis explicitly requires the latter.
- Identical finite positive profiles alone do not imply global
  automorphism conjugacy of an arbitrary finite ambient ring:
  a singleton and a doubleton in a three-atom Boolean ring
  give the standard counterexample.
- The ambient limit may have no greatest element. The original
  non-unital language uses only zero, addition, multiplication
  and the pairing; nothing in this reduction requires an
  ambient multiplicative identity.

The local finite swap regression
check_folkman_paired_bridge_swap_20261111.py
passed 1,717 compatible ambient symmetries, 24,280 commuting-square
comparisons, 21,536 complete pairing comparisons and 25,400
back-extension checks. It includes zero source sorts and unowned
target atoms, and refuses Python -O. A condensed regression was
committed under scripts/check_folkman_bridge_swap.py; that exact
committed script has NOT been run here. These tests are finite
semantics, NOT Lean kernel verification or independent adversarial
referee-agent certification.

## Remaining work to finish Track C

1. **Kernel gate:** locally install/use the pinned Lean 4 toolchain,
   build the new modules and BANANA.lean on the exact PR head,
   inspect every transitive axiom declaration and obtain genuinely
   independent adversarial proof reviews. The current container
   has no lean/lake/elan and github.com DNS is unavailable.
   No GitHub Actions were dispatched.
2. **Unconditional existence:** construct an actual countable
   original-language Folkman limit from the merged Track B finite
   HP/JEP/AP/countability certificate, or formalise a generic
   Fraïssé existence theorem that can be instantiated. Prove the
   particular limit has the directed finite-stage atlas and EPP.
   Mathlib's pinned Fraisse module has these notions but still
   lists limit existence as a TODO.
3. **Final orbit result:** instantiate the new conditional
   equivalence on that specific limit. The standard
   Ryll–Nardzewski implication to ω-categoricity can remain
   externally cited if permitted by the project.

This is a mathematically complete *conditional* finite-to-global
reduction, NOT an unconditional Lean proof of the countable limit.
**Keep PR #308 draft and unmerged. No manuscript green markers.**
