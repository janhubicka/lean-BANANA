# Track A close-out review — 8 November 2026

Internal note only. Do not insert into the frozen circulation manuscript.

## Work delivered

The shared finite-owner summation refactor is merged as PR #307.
The following work is staged together in draft PR #312:

1. Shared edge count to F2 conversion (`folkmanEdgeCount_cast`) in FolkmanPersistence, re-used by the existing tuple-profile theorem without changing its signature.
2. `folkmanComposeOwner` and exact fibre formula, with preservation of nonempty fibres.
3. `FolkmanAtomEmbedding.comp`, including the matrix pairing-preservation field, not merely a partial-map composition.
4. Identity owner and identity embedding, left/right identity and associativity, and embedding equality from its two owners.
5. Dedicated axiom audits and independent finite regressions. The new `check_folkman_owner_category_surjective_small.py` checks actual nonempty-fibre maps (1,113 composable triples, including 847 four-positive-sort triples).

No circulation text, appendix, TODO, marker or root `BANANA.lean` import was changed. All source changes are Lean modules, internal notes or regression scripts.

## Adversarial mathematical checks

- **Owner direction:** `f : A → B` is represented by `B.atom → Option A.atom`. Composition is `g(x).bind f`. This order matches embedding composition.
- **Missing owners:** `Option.none` propagates through composition. No element of a source fibre is contributed by an unowned final or intermediate atom.
- **Surjectivity/nonempty fibres:** For each source atom `i`, choose an intermediate atom with owner `i`, then a final atom owned by that intermediate atom.
- **Pairing:** The composite fibre is a disjoint union of intermediate fibres. Apply existing `folkmanEdgeCount_biUnion_left/right`, then cast each finite sum to `F2`, use `g.pairing_parity` pointwise, the shared edge-count conversion, and finally `f.pairing_parity`.
- **Identity:** The `some` identity owner's fibre at `i` is the singleton `{i}`, so pairing is the corresponding matrix entry.
- **Associativity:** Associativity of `Option.bind`; equality of records follows because the other fields are propositions and their owner maps agree.
- **Degenerate cases:** Empty left or right sorts give vacuous requirements, not a hidden positive-dimension assumption.
- **Statement scope:** This is an atom-coordinate category of pairing-preserving embeddings. It is **not yet** a proof that original-language non-unital ring embeddings are represented faithfully and compositionally. That native interface belongs to draft PRs #305 and #309.

## Verification still missing — non-negotiable merge gate

Local container inspection on 8 November found no `lean`, `lake` or `elan`. `git ls-remote https://github.com/janhubicka/lean-BANANA.git HEAD` failed with `Could not resolve host: github.com`. GitHub connector access was used only to inspect and edit the PR; no GitHub runner was invoked. **No Lean build or transitive-axiom audit of this head has been executed here.**

Run on the exact head commit:
```sh
python3 -m unittest discover -s scripts -p 'test_*.py'
python3 scripts/check_lean_module_graph.py
python3 scripts/check_folkman_edgecount_cast_small.py
python3 scripts/check_folkman_partial_owner_parity_small.py
python3 scripts/check_folkman_owner_composition_small.py
python3 scripts/check_folkman_embedding_composition_small.py
python3 scripts/check_folkman_owner_category_laws_small.py
python3 scripts/check_folkman_owner_category_surjective_small.py
lake build BANANA.NonPrecompact.FolkmanPartialOwnerComposition
lake build BANANA.NonPrecompact.FolkmanPartialOwnerCompositionAxiomAudit
lake build BANANA
bash scripts/audit_all_axioms_local.sh
```

Inspect the actual `#print axioms` outputs for each new declaration: only `propext`, `Classical.choice`, and `Quot.sound` are allowed. An **independent** adversarial reviewer must compare every exact theorem type against the intended claim and independently look for a missing hypothesis; the implementing assistant's inspection is not independent referee verification. If Lean flags elaboration, repair locally and repeat the exact-head gates.

## Track A completion judgement

**Mathematical interface and finite testing: implemented. Kernel verification, independent external refereeing and merge: not complete.** Keep #312 as draft; do not mark manuscripts validated. Do not treat the unresolved native PRs as a Track A blocker for merging the *shared* API once it is independently checked: they are downstream integration obligations.
