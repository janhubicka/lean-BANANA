# lean-BANANA — circulation-only archival companion

Lean formalisation by **Jan Hubička**, using OpenAI's ChatGPT 6 and 6.2, accompanying *Parity obstructions to precompact Ramsey expansions* by Sofia Brenner, Jan Hubička, Colin Jahel and Jaroslav Nešetřil. The author accepted statement-to-Lean correspondence on 27 November 2026 subject to the representation boundaries. See [the circulation scope](docs/circulation-only-scope.md), [classical dependencies](docs/classical-dependencies.md), [source provenance](docs/vendored-provenance.json), and [citation metadata](CITATION.cff). The code retains the original unconditional GLR proof; no new axiom or cited premise has been substituted. This candidate has not yet passed a fresh standalone Lean build.

## Reproduction

Install elan and the pinned toolchain (`leanprover/lean4:v4.35.0-rc3`). In a clean Git checkout, run:

```sh
lake exe cache get
bash scripts/verify_release_candidate.sh
```

For a downloaded source archive without Git metadata, initialise a clean local Git repository and commit the extracted files before running the strict audit; the resulting local commit ID need not equal the published release SHA. The archive and its release checksum identify the archived bytes.

The committed `lake-manifest.json` pins mathlib and its standard dependencies. Do not run `lake update`. The included successor-tree and abstract Ramsey-space source modules are the exact import closure used by the manuscript-linked declarations, not the full upstream developments. The full proof snapshot and previous strict run are documented in the scope note. The release gate includes source/blob checks, direct declaration/axiom audit, fresh kernel replay, named axiom audits, and regression tests. The project-owned BANANA code is Apache-2.0; the extracted code retains its original notices and permissions. See `LICENSE` and `licenses/`.
