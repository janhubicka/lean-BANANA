# Track C: verified classical Fraïssé-existence reference and porting audit
11 November 2026 — internal only, not a circulation-text change

## Significant external formalisation found

Cameron Freer's public Apache-2.0-licensed repository
https://github.com/cameronfreer/computable-model-theory
contains a completed classical Fraïssé-existence layer. Its
historical commit
a1fe76155a98f03933f7de0811e03b2473dd2e21
is PINNED TO THE SAME Lean toolchain as BANANA:
leanprover/lean4:v4.35.0-rc3.

The external exact-head "Lean Action CI" run
https://github.com/cameronfreer/computable-model-theory/actions/runs/37225534306
completed successfully. This is evidence for the external repository
at that particular source head, NOT a kernel build of BANANA.

Four reusable production files have Apache-2.0 headers, import
only Mathlib or each other, and are IDENTICAL (same Git blob SHA)
between external commits a1fe7615 (Lean 4.35.0-rc3) and
5d5f65ce (Lean 4.36.0-rc1):

1. ComputableModelTheory/ModelTheory/RepresentativeAge.lean
   131 lines, Git blob 31154f5a1d672d613cc3e434b2efb925db7f5761
2. ComputableModelTheory/ModelTheory/ExtensionRichFamily.lean
   151 lines, Git blob bf0f1a119f8b495fd6db49a8ce1aa0367a84db49
3. ComputableModelTheory/ModelTheory/ExtensionRichDirectLimit.lean
   174 lines, Git blob acf7c64b23900e3ae552ca6220a67a2901c91860
4. ComputableModelTheory/ModelTheory/FraisseExistence.lean
   311 lines, Git blob 26b295d21e522e4c203b5851f16241d43101ca15

Most relevant completed statements (namespace FirstOrder.Language):

* exists_fraisseSequence:
  A countable inhabited family F of finitely generated
  representatives, with COUNTABLE CARRIERS, JEP and AP,
  yields an increasing chain satisfying coverage and
  SequenceExtension. Heredity is not required for this theorem.
* exists_isFraisseLimit_representativeClass:
  Adds hereditary closure and a countable function signature,
  and supplies a COUNTABLE genuine Fraïssé limit of the
  representative class.
* exists_isFraisseLimit_of_isFraisse:
  Every IsFraisse class in a language with countably many
  function symbols has a countable IsFraisseLimit.
* isExtensionPair_directLimit and
  isUltrahomogeneous_directLimit:
  The stage extension squares imply the limit's actual
  embedding-extension/ultrahomogeneity properties.

The sequence construction explicitly schedules outgoing embeddings
from ALL historical stages (at Nat.pair m k), not only the
current stage. This is the missing fairness requirement in
our internal countable Folkman construction notes.

## Toolchain and Mathlib comparison

BANANA pins Lean 4.35.0-rc3 and official Mathlib at
5bd58ac291422a21f412ae354c91e7d172255a2c.
The external 4.35.0-rc3 version instead pins the
cameronfreer/mathlib4 fork at
346a4bd3f95e8591976c91259badc6d2c300f638.

The exact contents of three relevant Mathlib modules were compared:

- Mathlib/ModelTheory/Fraisse.lean: only two small differences
  in the fork (one explicit import and one proof tactic replacing
  a congruence application).
- Mathlib/ModelTheory/PartialEquiv.lean: one documentation-only
  wording difference in the inspected files.
- Mathlib/Order/Ideal.lean: one small proof-expression difference.

This makes a targeted port to BANANA's pinned Mathlib plausible.
It does NOT prove API compatibility or justify changing BANANA's
Mathlib pin. No Lean compiler is available in this container,
so no port has been elaborated, and no source was vendored here.

## Exact original-language adapter required

The external Fraïssé theorem is single-sorted FirstOrder.Language.
Our finite original-language Folkman class has TWO Boolean-ring
sorts and a pairing. A faithful one-sorted coding must be provided.

Suggested finite language:
- unary predicate Left (optionally also Right);
- two nullary function symbols 0_L and 0_R;
- four binary function symbols +_L, *_L, +_R, *_R;
- one binary relation PairingOne for β(x,y)=1 on Left×Right.

Interpret on Sum L R. For a wrong-sort argument, define each
function to return the corresponding named zero of its output
sort. Define PairingOne false off Left×Right.
All finite members are sums of two Boolean-ring carriers;
each sort is nonempty as a TYPE, including the one-element
zero ring. Tagged embeddings preserve the two subcarriers and
the correct zero, addition, multiplication and full β pairing.

One must PROVE (not postulate) the two directions of fidelity:

1. Native injective non-unital pairing homomorphisms induce
   embeddings of the coded FirstOrder.Language structures.
2. Every coded-language embedding restricts to actual native
   injective ring homomorphisms on both sorts preserving the
   entire F₂ pairing.

The tag relation and named zeros ensure that the finitely
generated language-substructures are exactly the pairs of
non-unital subrings, even if they omit the ambient units.
Use Track B's intrinsic-unit heredity theorem to show every
finite such substructure is a native finite Folkman object.

Then take the representative index
I = FolkmanAtomStructure, with
F A = the Sum-coded native finite pairing for A.
The merged Track B certificates supply:
- Countable I, Nonempty I (the 0,0 code);
- finite/therefore countable carriers;
- hereditary closure of finitely generated substructures;
- native JEP and AP with exact pairing diagrams.

The faithful translation of these diagrams is the major
adapter obligation. Applying the EXTERNAL theorem only
after that translation produces the countable tagged
Fraïssé limit, its finite-stage coverage and genuine
embedding extension. Decompose the tagged limit into its
left/right subcarriers, recover the original non-unital
ring operations and β, and discharge Track C's
FolkmanDirectedFiniteStageAtlas and FolkmanFiniteCodeEPP
(or derive generated homogeneity directly from
Mathlib IsFraisseLimit.ultrahomogeneous, bypassing the
cofinal bridge machinery).

## Comparison of implementation routes

A. Prefer the existing verified first-order existence theorem.
   Port its four independent classical modules with proper
   Apache-2.0 attribution under a separate Lean development,
   pinned to BANANA's existing toolchain and Mathlib.
   Prove the faithful finite-language adapter and instantiate
   exists_isFraisseLimit_representativeClass.
   The entire separate Track C finite-bridge back-and-forth
   construction becomes an optional check, not the only proof.

B. If the first-order encoding proves harder than the rest,
   specialise the external exists_fraisseSequence recursion
   directly to the category of native two-sort finite pairings.
   Preserve its historical-stage scheduling, AP/JEP step,
   actual two-sort pairing maps and direct-limit coherence.
   Do NOT copy a proof that only schedules embeddings out
   of the current stage: that is insufficient for finite EPP.

A is likely shorter and gives a reusable interface.
B avoids totalising operations on a Sum carrier but needs
a separate two-sort direct-limit structure.

Do not add the full external dependency through Lake:
the upstream historical package additionally depends
on InfinitaryLogic and its own Mathlib fork. Vendoring the
four classical Mathlib-only modules, with their licensing
headers and a pin-specific compilation gate, avoids
transitive version changes. Do not import code or migrate
Lean versions without exact-head local kernel verification.

## Verification and change-control gates

1. Locate a trusted local Lean 4.35.0-rc3 installation and
   the exact BANANA Mathlib cache.
2. In a SEPARATE draft branch, port the four Apache-2.0
   classical modules, compile each source and audit the
   axioms and required Mathlib import compatibility.
3. Implement and kernel-check the faithful Folkman
   single-sorted encoding, HP/JEP/AP translation, and
   representative-class finite-generation proof.
4. Instantiate the classical existence theorem and derive
   the directed atlas and EPP for the actual countable
   original-language Folkman limit.
5. Kernel-check the full Track C profile/orbit classification
   on that same head; obtain genuinely independent adversarial
   referee reviews before merging or marking the paper green.

Only source/API audits and reading a successful EXTERNAL
CI run were performed in this turn. No GitHub Actions
were launched for BANANA, no local Lean build was run,
and **no manuscript prose/TODOs/validation markers changed**.
