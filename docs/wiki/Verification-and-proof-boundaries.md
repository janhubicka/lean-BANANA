# Verification and proof boundaries

## Evidence

The verified proof snapshot is [`4fabdd7cf1bf1206912cd0d6c92e685b04e769cf`](https://github.com/janhubicka/lean-BANANA/commit/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf), Git tree `c4abf542fe7d09006f035694cda5f14f82ecd088`. The integrated commit [`4205b301a5960dbabe5bdf7fa226db85307ea87a`](https://github.com/janhubicka/lean-BANANA/commit/4205b301a5960dbabe5bdf7fa226db85307ea87a) has the identical tree. Documentation changes after this proof snapshot do not change that evidence.

| Verification measure | Result |
| --- | ---: |
| Lean files | 902 |
| Production modules | 515 |
| Production modules reachable from the public root | 511 |
| Audit-only proof modules | 4 |
| Unreachable production modules | 0 |
| Strict axiom-audit modules passed | 387/387 |
| Declaration queries | 1,435 |
| Distinct named declarations audited | 1,422 |
| Python unit tests | 12/12 |
| Exact-head CI steps | 261/261 |

The [strict CI run](https://github.com/janhubicka/lean-BANANA/actions/runs/45844957074) used the committed manifest, and the [post-merge CI](https://github.com/janhubicka/lean-BANANA/actions/runs/45854123551) passed 259 applicable steps. The strict audit parser accepts only `propext`, `Classical.choice` and `Quot.sound` in the audited transitive dependencies and checks that the declarations printed are exactly those requested. The [original audit artifact](https://github.com/janhubicka/lean-BANANA/actions/runs/45844957074/artifacts/15132656205) was also downloaded and its reports were rechecked against the exact source locally. Re-parsing archived logs is not a new Lean kernel run.

## Reading the paper's markers

- **Lean ✓**: a checked Lean statement corresponding to the mathematical claim or step being marked.
- **Lean rel.**: the linked theorem is checked in a related representation or under an explicit interface; the reader must also examine the correspondence and discharge any premises.
- **Lean part**: a checked component of a larger argument, not certification of every step of that argument.

A theorem passing the kernel and axiom audit can still have a different statement from the intended theorem. Statement fidelity is reviewed separately. The paper's human mathematical review is distinct from the final human review of the AI-produced Lean formalisation; the latter is pending at this snapshot.

## Main representation boundaries

| Area | Boundary |
| --- | --- |
| Finite classes | Atom and matrix presentations must preserve all operations, pairings, and actual image copies. The native finite-class theorems include arbitrary finite carriers in their stated representations. |
| Folkman limit | The first-order categorical limit is a product encoding; native rings, pairing and mixed-sort orbits are decoded from it. |
| BANANA model theory | The tagged relational complete theory and the functional age are not the same literal structure language. Sorted formula translation and decoding are explicit developments. |
| Generated expansion types | The native finite pointed-cover theorem is checked; the general many-sorted syntax-to-interface passage is an English mathematical argument. |
| General classical implications | The formalised instantiations and general theorems have their explicit hypotheses. Do not infer a general theorem from an instance or a conditional implication alone. |

The [mathematical representations chapter](Mathematical-representations.md) explains these choices.

## Classical results

The [classical-dependency audit](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/docs/classical-dependencies.md) records detailed endpoints. Among the checked developments are both directions of the countable categoricity/oligomorphicity correspondence, countable Witt extension, binary Graham–Leeb–Rothschild via the successor-tree theorem, invariant measures for dense directed unions of finite groups, amenability inheritance by open subgroups, clopen measure extension, pointwise orbit criteria, and the indicated canonical-amalgamation and DEERP implications. The general reverse metrisability implication of Ben Yaacov–Melleray–Tsankov's Theorem 1.1 remains a cited result; the concrete native BANANA nonmetrisability theorem has a checked direct proof.

## Statement-level review priorities

Review the three finite Fraïssé-class theorems on equal terms, the native expansion cover, exact copy/embedding degree statements, native coherent EPPA, and the dynamical/model-theoretic representation boundaries. Check quantifiers and assumptions, not just the theorem names. Important edge cases include zero rings, non-unital embeddings, degenerate pairings, zero-dimensional alternating spaces, and generated expanded domains larger than the distinguished copy.

No separate Folkman-specific mathematical proof obligation remains. No external journal referee report or completed final human Lean sign-off is claimed here.
