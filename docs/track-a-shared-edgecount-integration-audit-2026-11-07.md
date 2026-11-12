# Track A: shared Folkman edge-count cast — integration audit (7 November 2026)

This is an **internal development note**, not circulation manuscript prose.

## State and verification boundary

- PR #312 adds `folkmanEdgeCount_cast` to `FolkmanPersistence.lean` and makes the merged tuple-profile theorem `folkmanTuple_edgeCount_cast` a wrapper with **exactly the same statement**.
- Independent finite regression was **executed again** in the local container on 7 November: `python3 check_folkman_edgecount_cast.py` passed **37,477 / 37,477** instances, including `Fin 0`, empty blocks, and every binary incidence matrix with dimensions at most three. The repository copy of the same test is `scripts/check_folkman_edgecount_cast_small.py`.
- Git remote is inaccessible from the local container (`Could not resolve host: github.com`); `lean` and `lake` are absent. **No new exact-head Lean build, axiom audit or independent model-referee sign-off was obtained. Do not merge #312 yet.**
- The circulation paper and its appendix are untouched. Do not add a green marker on this evidence alone.

## Exact correspondence to native PR #305

The draft #305 theorem has the same mathematical statement as the specialization of the new generic lemma:

```lean
theorem folkmanNativeFin_edgeCount_cast
    (C : FolkmanAtomStructure)
    (X : Finset (Fin C.leftCount))
    (Y : Finset (Fin C.rightCount)) :
    (folkmanEdgeCount C.edge X Y : F2) =
      ∑ i ∈ X, ∑ j ∈ Y, C.edge i j := by
  exact folkmanEdgeCount_cast C.edge X Y
```

This is a proposed **proof replacement**, not an already applied patch to #305. Preserve the existing native theorem name for downstream compatibility. The common result does not mention atom ownership, non-unital maps or a preserved unit.

### Dependency and merge order

1. Compile and audit PR #312 at its exact head. Its shared lemma is already covered by a new `#print axioms` query in `FolkmanTupleProfilesPairingTransportAxiomAudit.lean`. Run `lake build BANANA` and `bash scripts/audit_all_axioms_local.sh`; allowed transitive axioms are only `propext`, `Classical.choice` and `Quot.sound`.
2. Independently check the statement and empty-sort cases. Check that no direct or indirect imports introduce unverified declarations.
3. Only after #312 passes, integrate the native code from #305 on top of the checked main and replace *only its proof* with the code above. PR #305 has separate outstanding compilation errors, so the shared cast cannot certify that PR.
4. Run the complete Lean and axiom gates again at the resulting integration SHA before merging.

## Adversarial observations

- The generic identity is a statement about finite incidence matrices, **not** about images of embeddings or the parity of unowned atoms. It must not be used as a surrogate for the actual non-unital morphism and pairing transport obligations.
- A direct cast of the natural-number *count* to `F2` is required; parity of the *total number of potential pairs* would be a different theorem.
- Empty `X` or `Y`, empty `Fin 0` sorts, and zero edges are included. No non-emptiness or unit hypotheses may be added silently.
- The regression tests arithmetic only. They do not test that the original Lean name resolves, that the proof elaborates, or that any higher-level native theorem is sound.
