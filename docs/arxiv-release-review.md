# Release candidate review (26 November 2026)

Scope: circulation manuscript at `a4fd4ee350bb88c210e1c017c1ed4a82e19b53f2`. No manuscript edits. This is a source-level correspondence/self-audit, not an independently spawned referee or a Lean build.

## Draft pull requests

| PR | Release disposition | Evidence and remaining scope |
| --- | --- | --- |
| #308 (Folkman finite profiles and global orbits) | Superseded for v1 | `FolkmanFirstOrderExistence.exists_folkmanFirstOrderLimit_categorical` (declaration in the `SuccessorTree.NonPrecompact` namespace) constructs the countably infinite categorical encoded limit, and `FolkmanFirstOrderTaggedLimitOrbits.lean` obtains finite native tagged tuple-orbit representatives. Alternate bridge/atlas developments can remain in branch history. |
| #310 (coherent EPPA class-index descent) | Superseded for v1 | `BananaNativeCoherentEppa.lean`: `BananaNative.exists_coherentEppaWitness` supplies a single native perfect witness, pairing-preserving maps and a coherent assignment for actual subpairs. The earlier groupoid kernel is optional reusable work. |
| #311 (symplectic strong AP) | Not needed for v1 | `SymplecticCopySystem.lean` proves actual alternating-space AP, which is enough for degree propagation, and the paper uses the hereditary age including degenerate spaces. Exact strong intersection is stronger than the needed AP and should not be claimed from this theorem. |
| #312 (Folkman owner composition/refactoring) | Defer | Code reuse and additional atom-category laws are not needed for the verified finite-class certificate. |
| #319 (coordinate invariance) | Defer/retain | The native matrix classification is checked and the functional age transfer verifies the ranges and composition. The standalone invariance theorem would be useful but is not needed to release the manuscript with the current explicit representation boundary. |
| #321 (Mathlib bilinear-map calculus) | Defer | Useful cleanup; no release dependency. |

Do not merge unverified branches to make the release checklist appear complete. Closing as superseded or deferred does not assert that every stronger auxiliary result has been formalised on main.

## Manuscript changes since the last baseline

* `folkman-limits.tex`: homogeneity with zero right ring still gives the required orbit of proper nonzero left elements. The native proof uses the same interval stabiliser and Stone-space contradiction. The shortened English proof uses the finite extension property for two/three-piece partitions.
* `banana-eppa.tex`: cofinal perfect-total systems with AP and JEP give WAP and JEP for all systems. Enlarging both targets after taking the cofinal extension yields an amalgam agreeing on that extension, hence on the original source.
* `persistent-colouring.tex`: renaming bound affine-coordinate variables from x,y to u,v does not change the residue lemma or its hypotheses.
* `pre-banana-dynamics.tex`: moving mass realisation and the non-co-precompactness proof before Stone dynamics does not alter hypotheses. The distinct masses (2/p^k) lie in one reduct orbit (zero mark, nonzero proper element) and distinct mass-preserving orbits. For the stabiliser U of x_1, the elements g_k^{-1} lie in distinct U--A_S double cosets. The native subgroup theorem supplies the same conclusion.

## Release boundaries

The generated-expansion bound directly counts distinguished native copies inside expanded generated domains. For a hereditary many-sorted expansion, each copy generates a member of the expanded age; a pointed expanded isomorphism to a representative followed by inclusion maps its distinguished reduct copy to the given native copy. Reduction respects composition and the expansion class's Ramsey property is the embedding Ramsey property. This is the explicit mathematical correspondence; a full many-sorted syntax adapter is not claimed.

The new native pointed-cover interface allows a family with a uniform number of representatives for each expanded target. An expansion with finitely many global generated pointed types satisfies this: use all global types, including those not occurring in the chosen target. The bound does not need uniqueness of the representative or reasonableness of the expansion. If a positive finite count is needed for a target with no copies, use the global list; the source itself admits an expansion so the global collection is nonempty.

The unconditional embedding-degree classification combines the matrix copy-degree classification (including exclusion of degree zero) with the uniform embedding fibres, whose cardinality is the number of reduct automorphisms. It remains pending an exact-head Lean check.

The CFF metadata uses a collective software attribution and names the four manuscript authors as the preferred unpublished citation. Confirm individual software credit, arXiv identifier and release version before archiving. No DOI or publication date is asserted.
