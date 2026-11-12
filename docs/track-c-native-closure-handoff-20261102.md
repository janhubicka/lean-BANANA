# Track C: native non-unital generated-subring bridge

Status: **draft source; no Lean kernel verification**.
Parent: `cc3670f2ceb1f09683de777606cf261080c2ad20` (PR #308).
No manuscript, appendix, TODO or validation-marker file is changed.

## Mathematical construction

The previous restricted Boolean terms have truth value false at the
all-zero signature, but their syntax still contains one and complement.
This does not on its own identify their value range with a native
non-unital ring closure. The new source supplies that missing argument.

For a Boolean term t, write c=t(0). The compiler constructs a ring term
r using only zero, generators, addition and multiplication such that
r(p)=t(p)+c over F2. Complement leaves r unchanged and flips c. If the
subterms have centred parts r,s and constants c,d, the centred part of
their product is

    r*s + c*s + d*r.

The centred part of their Boolean join is r+s plus that expression.
Neither multiplication by a Boolean constant in this formula nor the
compiler implementation adjoins a unit: c*s is implemented as s or zero.
For c=0 the compiled ring term evaluates exactly like t. This proves
that every restricted term value is a genuine non-unital ring-term value.
The reverse translation expresses addition as Boolean symmetric difference.

In any native BooleanRing, genuine ring-term values form a
NonUnitalSubring: they contain zero and the generators, are closed under
addition and multiplication, and are closed under negation since -x=x.
Minimality and induction on ring terms identify this subring with
NonUnitalSubring.closure (Set.range xs). This argument needs neither
finiteness nor nontriviality.

Equal ring-term equation kernels then give an actual ring equivalence
between native generated subrings by interpreting the same term. The
source proves well-definedness in both directions, inverse laws,
addition, multiplication and named-generator preservation. The earlier
finite profile theorem supplies the kernel equality on finite atom models.
Choosing ring-term representatives also transfers the existing all-term
pairing result to every pair of elements of those native generated subrings.

## New source modules

- FolkmanNonunitalRingTerms: genuine syntax, native closure minimality,
  atom interpretation and operation-preserving-map naturality.
- FolkmanNonunitalTermNormalisation: unit-elimination compiler, both
  syntax translations, and identification with native non-unital closure.
- FolkmanGeneratedNonunitalRingIso: generic native ring equivalence and
  its finite-signature specialisation.
- FolkmanGeneratedNonunitalPairing: full two-sort pairing preservation
  on native generated-subring carriers in finite atom presentations.
- FolkmanGeneratedNonunitalAxiomAudit: 22 exact declaration audit requests.

The existing FolkmanTupleTermPairIsoAxiomAudit imports the new audit.
It is already imported by BANANA.lean, making the new modules transitively
reachable without editing the umbrella file or another track's modules.

## Executed local checks

The baseline script was copied byte-for-byte from the parent. Its Git
blob hash is `01cefd421b5c7da642de3c0a1de670320d29356b`.

    python3 scripts/check_folkman_tuple_term_completeness_small.py

Passed: 689 generated-ring cases, 9,170 pairing cases and 9,607
profile-equivalent comparisons.

    python3 scripts/check_folkman_nonunital_normalisation.py

Passed: all 278 Boolean functions on zero to three variables; 131,624
binary-constructor semantic checks; 5,000 seeded syntactic terms on zero
to four variables; 689 generated-closure and finite powerset-ring
isomorphism cases; 39,400 addition/multiplication checks; 1,940
named-generator checks. Cases include self-isomorphisms and trivial rings.
These are separate Python semantic implementations, NOT execution of Lean.

## Review boundaries and remaining gates

The source and mathematical argument were self-audited. No independent
referee agent was spawned: none was available through the current tools.
Do not describe alternative arguments or finite tests as independent
referee certification.

The current runtime has no Lean, Lake or Elan binary; a checkout attempt
failed because the container could not resolve github.com. Repository
source was read through the GitHub connector. No complete repository
checkout, full module-graph run, Lean elaboration or transitive axiom audit
was performed. No workflow was dispatched. The commit requests CI skipping.

Pinned configuration inspected: Lean 4.35.0-rc3; successor-tree dependency
`d9be105f73ca5a0f3f411b87d4c2419d0eb94753`, whose mathlib pin is
`5bd58ac291422a21f412ae354c91e7d172255a2c`. NonUnitalSubring and BooleanRing
APIs were inspected at that exact mathlib revision.

Before any merge or manuscript marker: run the full local module-graph
check, `lake build BANANA`, `bash scripts/audit_all_axioms_local.sh`, both
regression scripts, and independent exact-statement/referee reviews.
The dependent PR #306 must pass the same checks.

Further work is still required to instantiate the finite-code result on
both original native carriers through Track B's coordinate interfaces,
and to construct/use the homogeneous countable Folkman limit. No global
automorphism-orbit or omega-categoricity result is asserted by this change.
