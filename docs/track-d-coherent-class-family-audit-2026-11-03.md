# Track D — coherent class-family continuation, 3 November 2026

Internal audit only. This is NOT circulation prose, a Lean kernel check, or
independent referee sign-off. No TeX file, existing validation marker or
manuscript TODO has been modified or reintroduced.

## Newly staged formal statements

1. BananaMatrixCoherentChoiceLemmas: with an embedding of A into the
   fixed perfect B_n and l+r <= n, the existing aligned-completion theorem
   supplies ONE homomorphism extending all automorphisms of A. Perfect-pair
   homogeneity supplies a pairing-preserving ambient conjugator aligning
   each isomorphic embedded copy simultaneously on the left and right.
2. BananaMatrixCoherentOneClass: uses those existential results to choose
   one group homomorphism for an entire isomorphism class and one conjugator
   per object. It constructs the assignment Theta and states its extension,
   identity, composition and inverse laws on all typed isomorphisms.
3. BananaMatrixCoherentClassFamily: chooses these assignments for each
   class index, with all extensions landing in the SAME ambient B_n.
   Composable isomorphisms necessarily belong to one class.
4. BananaMatrixCoherentOneClassAxiomAudit: adds exact transitive-axiom
   queries, but no claim that the queries were executed.

The hypotheses are explicit. The class-family theorem assumes that one
has already classified actual finite substructures into classes with
finite two-sorted coordinate presentations, embeddings into B_n and
pairing-preserving isomorphisms from their chosen representatives. These
objects are NOT yet constructed as a typed finite family in Lean. Thus
the theorem is conditional and does NOT yet prove the manuscript's full
coherent-EPPA theorem.

## Independent finite experiment and adversarial counterexample

The previous simultaneous-choice regression was re-executed on 3 November:
17 pairing matrices, 1,277 partial isomorphisms and 82,697 composable
pairs. It passed in both normal and python -O modes.

The additional zero-pairing regression tests all 30 ambient/dimension
triples with n <= 3 and l,r <= n. A zero pairing of dimensions l and r
embeds in B_n if and only if l+r <= n. This gives a sharpness obstruction
for the original side-dimension bound; in particular a (1,1) zero pairing
does not embed in B_1 but does embed in B_2. This is a computation,
not a Lean proof.

## Two logical audit passes; not independently spawned model referees

Statement-fidelity pass: the new one-class result no longer assumes
an ambient action or conjugators, but does assume chosen representative
isomorphisms and embeddings into a common B_n. The family result similarly
assumes the class index and all its coordinate data. Neither result alone
implies the full circulation theorem without a total identification with
actual substructures and partial isomorphisms.

Counterexample pass: arbitrary carrier permutations do not preserve the
pairing, separate conjugators for left and right need not form an ambient
automorphism, choosing different extension maps for separate arrows can
violate composition, and a zero pairing can force the full dimension
bound. These hazards are all represented by explicit hypotheses rather
than concealed behind a stronger theorem label.

## Next integration step and kernel gate

Construct the actual finite subpair representation of a fixed finite A,
including both subspace embeddings and transported pairings. Partition
these objects by isomorphism, select a representative for each class,
provide the coordinate maps and prove that every genuine partial
automorphism yields exactly one arrow in the class-indexed type. For
the original A of dimensions L,R the common witness is B_(L+R);
each subpair dimension satisfies l<=L and r<=R.

Run locally on the *exact* PR head using the pinned Lean toolchain:
  python3 scripts/check_lean_module_graph.py
  lake env lean BANANA/NonPrecompact/BananaMatrixCoherentOneClassAxiomAudit.lean
  lake env lean BANANA/NonPrecompact/BananaMatrixCoherentTransportAxiomAudit.lean
  lake build BANANA
  bash scripts/audit_all_axioms_local.sh
  python3 scripts/check_banana_coherent_choices.py
  python3 -O scripts/check_banana_coherent_choices.py
  python3 scripts/check_banana_zero_pairing_witness_bound.py

Lean/Lake were not available in the executing container. Therefore new
declarations remain UNCOMPILED and UNVERIFIED. No GitHub Actions may be
used. Do not merge, or mark the printed EPPA theorem fully verified,
until compilation, all-transitive-axiom audit, and genuinely independent
statement-fidelity/counterexample reviews succeed.
