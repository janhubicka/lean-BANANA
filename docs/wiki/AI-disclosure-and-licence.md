# AI disclosure, responsibility and licence

## AI assistance

The Lean formalisation in this repository was carried out by **Jan Hubička** using **OpenAI's ChatGPT 6 and 6.2**. ChatGPT assisted with the mathematical representations, Lean definitions and proofs, auxiliary lemmas, verification scripts, and documentation. Lean's kernel checks the resulting declarations. On 27 November 2026, Jan Hubička accepted the correspondence between the manuscript's statements and the formalised theorems on the basis of the adversarial audit and verified declaration crosswalk, subject to the documented representation boundaries. This disclosure concerns the Lean development and does not replace the article's separate AI-assistance statement. The authors remain responsible for the mathematical arguments in the article.

The verification evidence is the actual checked Lean code and its kernel/axiom reports, not an assertion of correctness by the language model. The source-level representation and statement boundaries are described in [Verification and proof boundaries](Verification-and-proof-boundaries.md).

## Software licence

The project-owned Lean source and verification scripts are licensed under [Apache-2.0](https://github.com/janhubicka/lean-BANANA/blob/4fabdd7cf1bf1206912cd0d6c92e685b04e769cf/LICENSE). The two project-owned Lean dependencies, [lean-successors](https://github.com/janhubicka/lean-successors) and [lean-ramsey-space-todorcevic](https://github.com/janhubicka/lean-ramsey-space-todorcevic), also use Apache-2.0; earlier permissions, including the prior CC0 dedication in lean-successors, are preserved. Third-party dependencies retain their respective licences and notices. The manuscript has a separate publication licence.

## Citation

Use the article for its mathematical statements and exposition. Cite Jan Hubička for the Lean formalisation, together with the exact checked source revision or the versioned `arxiv-v1` release once published. The [citation metadata](https://github.com/janhubicka/lean-BANANA/blob/main/CITATION.cff) records Jan Hubička as software author and the four manuscript authors separately. The existing Apache-2.0 licence and third-party notices are retained. No DOI or arXiv identifier is asserted before it exists.

The verified proof revision is [`fc0972fda0cc25ab94ab7315f6f57b7eed9127b9`](https://github.com/janhubicka/lean-BANANA/commit/fc0972fda0cc25ab94ab7315f6f57b7eed9127b9).
