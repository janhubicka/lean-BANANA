# BANANA — Lean formalisation of parity obstructions to precompact Ramsey expansions

This wiki accompanies *Parity obstructions to precompact Ramsey expansions* by Sofia Brenner, Jan Hubička, Colin Jahel and Jaroslav Nešetřil. It explains the mathematics checked in the Lean companion, the representations used for finite structures and their limits, and the precise boundaries of the formalisation. It is intended for readers of the article as well as mathematicians who wish to reuse the library.

## Read the formalisation

| Chapter | Content |
| --- | --- |
| **[Formalised statements](Formalised-statements.md)** | Crosswalk from the circulation paper's results to pinned Lean declarations, including their scope and hypotheses |
| **[Proof architecture](Proof-architecture.md)** | The mathematical constructions behind the formalisation, from atom grids and bilinear pairings to persistent colourings and dynamics |
| **[Mathematical representations](Mathematical-representations.md)** | Original languages, finite coordinates, genuine copies, first-order encodings, and generated expansion types |
| **[Verification and proof boundaries](Verification-and-proof-boundaries.md)** | Kernel and axiom checks, classical dependencies, relative and partial marks, author correspondence acceptance |
| **[Using the library](Using-the-library.md)** | Pinned dependencies, reproducible verification, imports and main declaration endpoints |
| **[AI disclosure and licence](AI-disclosure-and-licence.md)** | How the Lean formalisation was produced, responsibility, software licensing and citation |
| **[Publishing](Publishing.md)** | How the version-controlled documentation is synchronised with this Wiki |

## Main mathematical results

- Boolean–BANANA, Folkman–BANANA and BANANA: finite age and amalgamation, countable limits and orbit/categoricity results in the representations described in this wiki.
- Persistent colourings yielding infinite Ramsey degree in all three classes; obstructions to precompact Ramsey expansions, including the generated-domain notion needed for expansions by functions and constants.
- BANANA: coherent EPPA, an amenable automorphism group with ample generics, no co-precompact extremely amenable subgroup, and a nonmetrisable universal minimal flow.
- Exact copy and embedding Ramsey degrees for BANANA and finite alternating spaces over the two-element field.
- BANANA's definable elementary embedding Ramsey property (DEERP) and invariant enumeration types, in the stated first-order and sorted settings.
- Boolean–BANANA: failure of the generic point property and continuum many conjugacy classes of closed maximal amenable subgroups.

Read the [statement crosswalk](Formalised-statements.md) for the exact representation and interface used by each result. In particular, the arbitrary many-sorted generated-expansion correspondence is explained mathematically rather than claimed as a separate formal syntax adapter.

## Verification

The release proof snapshot is [`fc0972fd`](https://github.com/janhubicka/lean-BANANA/commit/fc0972fda0cc25ab94ab7315f6f57b7eed9127b9). Its [strict CI run 46049836518](https://github.com/janhubicka/lean-BANANA/actions/runs/46049836518) passed all verification gates, including fresh kernel replay, 10,230 directly audited visible declarations in 559 modules, all 363 manuscript-linked declarations (covering 299 markers), 387 named axiom-audit modules, and 29 Python tests. All 515 production modules are reachable. Only `propext`, `Classical.choice` and `Quot.sound` occur in the audited transitive dependencies. The direct inventory excludes 2,676 inaccessible private constants; fresh kernel replay nevertheless passed. The [audit archive](https://github.com/janhubicka/lean-BANANA/actions/runs/46049836518/artifacts/15227531922) was re-parsed locally and its SHA-256 checked: `d7b6b35d64c2a780765a762d4474170afd882f7c33634d672324a122ab0b0b8c`. The correspondence acceptance does not assert that every sentence of the article is formalised.

The [repository proof map](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/README.md#proof-coverage) has more detailed declaration links. The [classical-dependency audit](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/docs/classical-dependencies.md) describes general theorems used in the paper and their checked counterparts.

## AI disclosure and licence

The Lean formalisation in this repository was carried out by **Jan Hubička** using **OpenAI's ChatGPT 6 and 6.2**. ChatGPT assisted with the mathematical representations, Lean definitions and proofs, auxiliary lemmas, verification scripts, and documentation. Lean's kernel checks the resulting declarations. On 27 November 2026, Jan Hubička accepted the correspondence between the manuscript's statements and the formalised theorems on the basis of the adversarial audit and verified declaration crosswalk, subject to the documented representation boundaries. This disclosure concerns the Lean development and does not replace the article's separate AI-assistance statement. The authors remain responsible for the mathematical arguments in the article.

The project-owned Lean source and verification scripts are licensed under [Apache-2.0](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/LICENSE). The two project-owned Lean dependencies, [lean-successors](https://github.com/janhubicka/lean-successors) and [lean-ramsey-space-todorcevic](https://github.com/janhubicka/lean-ramsey-space-todorcevic), also use Apache-2.0; earlier permissions, including the prior CC0 dedication in lean-successors, are preserved. Third-party dependencies retain their respective licences and notices. The manuscript has a separate publication licence.

The source of truth for this wiki is the version-controlled `docs/wiki/` directory. See [Publishing](Publishing.md) for the automatic synchronisation workflow.
