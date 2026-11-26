# BANANA — Lean formalisation of parity obstructions to precompact Ramsey expansions

This wiki accompanies *Parity obstructions to precompact Ramsey expansions* by Sofia Brenner, Jan Hubička, Colin Jahel and Jaroslav Nešetřil. It explains the mathematics checked in the Lean companion, the representations used for finite structures and their limits, and the precise boundaries of the formalisation. It is intended for readers of the article as well as mathematicians who wish to reuse the library.

## Read the formalisation

| Chapter | Content |
| --- | --- |
| **[Formalised statements](Formalised-statements.md)** | Crosswalk from the circulation paper's results to pinned Lean declarations, including their scope and hypotheses |
| **[Proof architecture](Proof-architecture.md)** | The mathematical constructions behind the formalisation, from atom grids and bilinear pairings to persistent colourings and dynamics |
| **[Mathematical representations](Mathematical-representations.md)** | Original languages, finite coordinates, genuine copies, first-order encodings, and generated expansion types |
| **[Verification and proof boundaries](Verification-and-proof-boundaries.md)** | Kernel and axiom checks, classical dependencies, relative and partial marks, remaining human correspondence review |
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

The proof documentation is pinned to [commit `4fabdd7cf1`](https://github.com/janhubicka/lean-BANANA/commit/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf). Its [complete strict CI run](https://github.com/janhubicka/lean-BANANA/actions/runs/45844957074) passed 387 axiom-audit modules, 1,435 declaration queries and 12 Python tests. The audited dependencies use only the standard Lean axioms `propext`, `Classical.choice` and `Quot.sound`. The merge into main had an identical source tree and passed its own CI run. These are checks of Lean declarations, not a claim that every sentence of the article has been formalised.

The [repository proof map](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/README.md#proof-coverage) has more detailed declaration links. The [classical-dependency audit](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/docs/classical-dependencies.md) describes general theorems used in the paper and their checked counterparts.

## AI disclosure and licence

The Lean formalisation in this repository was produced by **OpenAI's ChatGPT**, referred to in the manuscript as **Řehořek**, under the direction of the authors. ChatGPT was used to develop the mathematical representations, Lean definitions and proofs, auxiliary lemmas, verification scripts, and documentation. Lean's kernel checks the resulting declarations. The human authors are responsible for the paper and for reviewing the correspondence between its statements and the formalised theorems; final human review of the formalisation is pending. This disclosure concerns the Lean development, and does not replace the article's separate AI-assistance statement.

The project-owned Lean source and verification scripts are licensed under [Apache-2.0](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/LICENSE). The two project-owned Lean dependencies, [lean-successors](https://github.com/janhubicka/lean-successors) and [lean-ramsey-space-todorcevic](https://github.com/janhubicka/lean-ramsey-space-todorcevic), also use Apache-2.0; earlier permissions, including the prior CC0 dedication in lean-successors, are preserved. Third-party dependencies retain their respective licences and notices. The manuscript has a separate publication licence.

The source of truth for this wiki is the version-controlled `docs/wiki/` directory. See [Publishing](Publishing.md) for the automatic synchronisation workflow.
