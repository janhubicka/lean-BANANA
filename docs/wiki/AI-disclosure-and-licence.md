# AI disclosure, responsibility and licence

## AI assistance

The Lean formalisation in this repository was produced by **OpenAI's ChatGPT**, referred to in the manuscript as **Řehořek**, under the direction of the authors. ChatGPT was used to develop the mathematical representations, Lean definitions and proofs, auxiliary lemmas, verification scripts, and documentation. Lean's kernel checks the resulting declarations. The human authors are responsible for the paper and for reviewing the correspondence between its statements and the formalised theorems; final human review of the formalisation is pending. This disclosure concerns the Lean development, and does not replace the article's separate AI-assistance statement.

The verification evidence is the actual checked Lean code and its kernel/axiom reports, not an assertion of correctness by the language model. The source-level representation and statement boundaries are described in [Verification and proof boundaries](Verification-and-proof-boundaries.md).

## Software licence

The project-owned Lean source and verification scripts are licensed under [Apache-2.0](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/LICENSE). The two project-owned Lean dependencies, [lean-successors](https://github.com/janhubicka/lean-successors) and [lean-ramsey-space-todorcevic](https://github.com/janhubicka/lean-ramsey-space-todorcevic), also use Apache-2.0; earlier permissions, including the prior CC0 dedication in lean-successors, are preserved. Third-party dependencies retain their respective licences and notices. The manuscript has a separate publication licence.

## Citation

Use the article for its mathematical statements and exposition. Cite the Lean repository together with the exact checked source revision (or the approved versioned release when available). The [citation metadata](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/CITATION.cff) records the collective software attribution and manuscript authors. Final release metadata and individual software attribution are subject to author approval. No DOI or arXiv identifier is asserted before it exists.

The currently documented verified proof revision is [`4fabdd7cf1bf1206912cd0d6c92e685b04e769cf`](https://github.com/janhubicka/lean-BANANA/commit/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf).
