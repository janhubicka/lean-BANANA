# Verification and proof boundaries

## Evidence

The release proof snapshot is [`fc0972fd`](https://github.com/janhubicka/lean-BANANA/commit/fc0972fda0cc25ab94ab7315f6f57b7eed9127b9). Its [strict CI run 46049836518](https://github.com/janhubicka/lean-BANANA/actions/runs/46049836518) passed all verification gates, including fresh kernel replay, 10,230 directly audited visible declarations in 559 modules, all 363 manuscript-linked declarations (covering 299 markers), 387 named axiom-audit modules, and 29 Python tests. All 515 production modules are reachable. Only `propext`, `Classical.choice` and `Quot.sound` occur in the audited transitive dependencies. The direct inventory excludes 2,676 inaccessible private constants; fresh kernel replay nevertheless passed. The [audit archive](https://github.com/janhubicka/lean-BANANA/actions/runs/46049836518/artifacts/15227531922) was re-parsed locally and its SHA-256 checked: `d7b6b35d64c2a780765a762d4474170afd882f7c33634d672324a122ab0b0b8c`. The correspondence acceptance does not assert that every sentence of the article is formalised.

| Verification measure | Result |
| --- | ---: |
| Lean files | 902 |
| Production modules reachable | 515/515 |
| Audit-only or unreachable production modules | 0 |
| Visible declarations directly audited | 10,230 |
| Direct manuscript declaration requirements | 363/363 |
| Fresh kernel replay | Passed |
| Named axiom-audit modules | 387/387 |
| Named declaration queries | 1,435 |
| Distinct named declarations | 1,422 |
| Python tests | 29/29 |

The integrated main commit `15a4468591f703bf55cadf9f7fefa7890a7e1f54` has the identical Git tree as the checked proof snapshot. The earlier verified revision `4fabdd7cf1` remains valid historical evidence. Documentation changes after the proof snapshot do not change the Lean proof sources or dependency pins; distinguish them from exact-head kernel verification. Re-parsing archived logs is not a new Lean kernel run.

## Reading the paper's markers

- **Lean ✓**: a checked Lean statement corresponding to the mathematical claim or step being marked.
- **Lean rel.**: the linked theorem is checked in a related representation or under an explicit interface; the reader must also examine the correspondence and discharge any premises.
- **Lean part**: a checked component of a larger argument, not certification of every step of that argument.

A theorem passing the kernel and axiom audit can still have a different statement from the intended theorem. Statement fidelity is reviewed separately. Jan Hubička accepted the statement-to-Lean correspondence on 27 November 2026 on the basis of the adversarial audit and verified declaration crosswalk, subject to the documented representation boundaries. This records acceptance, not a claim that every declaration was independently inspected by the author.

## Main representation boundaries

| Area | Boundary |
| --- | --- |
| Finite classes | Atom and matrix presentations must preserve all operations, pairings, and actual image copies. The native finite-class theorems include arbitrary finite carriers in their stated representations. |
| Folkman limit | The first-order categorical limit is a product encoding; native rings, pairing and mixed-sort orbits are decoded from it. |
| BANANA model theory | The tagged relational complete theory and the functional age are not the same literal structure language. Sorted formula translation and decoding are explicit developments. |
| Generated expansion types | The native finite pointed-cover theorem is checked; the general many-sorted syntax-to-interface passage is established in the manuscript but has not been formalised in Lean. |
| General classical implications | The formalised instantiations and general theorems have their explicit hypotheses. Do not infer a general theorem from an instance or a conditional implication alone. |

The [mathematical representations chapter](Mathematical-representations.md) explains these choices.

## Classical results

The [classical-dependency audit](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/docs/classical-dependencies.md) records detailed endpoints. Among the checked developments are both directions of the countable categoricity/oligomorphicity correspondence, countable Witt extension, binary Graham–Leeb–Rothschild via the successor-tree theorem, invariant measures for dense directed unions of finite groups, amenability inheritance by open subgroups, clopen measure extension, pointwise orbit criteria, and the indicated canonical-amalgamation and DEERP implications. The general reverse metrisability implication of Ben Yaacov–Melleray–Tsankov's Theorem 1.1 remains a cited result; the concrete native BANANA nonmetrisability theorem has a checked direct proof.

## Statement-level review priorities

Review the three finite Fraïssé-class theorems on equal terms, the native expansion cover, exact copy/embedding degree statements, native coherent EPPA, and the dynamical/model-theoretic representation boundaries. Check quantifiers and assumptions, not just the theorem names. Important edge cases include zero rings, non-unital embeddings, degenerate pairings, zero-dimensional alternating spaces, and generated expanded domains larger than the distinguished copy.

No separate Folkman-specific mathematical proof obligation remains. The author correspondence acceptance is recorded above; no external journal referee report is claimed.

## Two notions of finite expansion types

Some earlier parts of the library, including `IsReasonablePrecompactRamseyAge` in `FirstOrderFunctionalRamseyAge.lean` and `cylinder_exists_namedFunctionalRamseyAge` in `BooleanBananaFirstOrderAge.lean`, use **same-carrier** finite expansion counts. With added functions or constants, a finite reduct copy may generate a larger expanded domain. The paper instead counts isomorphism types of those generated domains with the reduct copy distinguished. The older named functional expansion theorem does not assert finiteness of these generated types and is not a counterexample to the non-precompactness theorems. The generated-type and native pointed-cover results, not the legacy same-carrier name, specify the circulation claims.
