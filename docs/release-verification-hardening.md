# Release-verification hardening (27 November 2026)

This change responds to the supplied adversarial audit of the circulation proof companion. The previous strict run at 4fabdd7cf1 remains evidence for that exact revision; the new workflow is a candidate until its own full run passes.

- One strict workflow for pull requests, main pushes, tag pushes and manual dispatch. Ordinary feature-branch pushes do not duplicate PR checks. No legacy branch workflows run lake update.
- Dependency-only caching keyed by toolchain, Lake configuration and manifest, with no cross-manifest restore and saves only on main. The root library is built from source; actual dependency revisions and clean tracked source are checked.
- Every production module must be reachable from BANANA.lean; named axiom audit entry points must not be imported by the production root. Every named audit report is parsed against its exact declaration multiset.
- A separate audit command uses Lean.collectAxioms (the implementation of #print axioms) on every visible project-owned declaration in the BANANA import closure. The inventory lists module, declaration and allowed axioms. It also reports unavailable private constants. This is broader than the list of intermediate manuscript declarations, but matching every manuscript marker to an inventory entry remains a separate gate.
- Fresh Lean kernel replay with leanchecker --fresh BANANA, lexical hygiene scanning, the existing regression checks, unit tests and archived exact-head logs. The replay is performed by Lean's own kernel, not an independent external verifier.
- Seven incorrect wiki anchors repaired against the already verified 4fabdd7cf1 snapshot. Do not repin the wiki or manuscript to the new source until strict verification and statement crosswalk review are complete.

No mathematical theorem statements or proof bodies were modified. Source-level review and a successful CI run do not by themselves establish correspondence to the paper. The manuscript prose remains frozen.
