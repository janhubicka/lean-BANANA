# Abstract pre-BANANA strong amalgamation: proof obligations and adversarial audit

11 October 2026. Internal validation note; **not circulation prose**.

## Mathematically complete transfer argument

Let `A → B` and `A → C` be embeddings of nontrivial finite Boolean
algebras with additive `F₂` parity maps, vanishing on `0` and `1`.
The intended conclusion is a strong amalgam in the original Boolean
language with the parity predicate, not merely an atom-grid amalgam.

1. **Coding objects.** Every nontrivial finite Boolean algebra is
   isomorphic to the powerset of its nonempty finite set of atoms. Its
   parity map is the sum of its values on those atoms, whose total is
   zero. Enumerating atoms gives the marked `Fin n` structure
   `prebananaAbstractAtomCode`. The code of each Boolean element is
   its finite set of atom indices. Its parity is the original parity.
   These assertions are established by the merged object-code and
   literal atom-sum modules.
2. **Coding embeddings.** Any unital injective Boolean map is the
   inverse-image map of a surjection from target atoms to source atoms.
   Each source atom has a nonempty target fibre. Preservation of the
   parity predicate implies that the sum of the target markings in each
   fibre equals the marking of that source atom. Enumerating atoms
   transports the partition and every fibre sum to a genuine
   `PrebananaAtomEmbedding`.
3. **Naturality.** Write `c_A,c_B,c_C` for the Boolean element codes,
   and `f',g'` for the induced atom-coordinate embeddings. One must
   prove for **every** Boolean element, not merely each atom:
   `c_B(f(x)) = prebananaBooleanMap(f',c_A(x))`, and analogously for
   `g`. This is the precise commuting-square obligation.
4. **Use the proven powerset strong amalgam.** The finite marked grid
   gives an atom structure `D'` and marked atom embeddings
   `u:B'→D'`, `v:C'→D'` such that their powerset maps commute over
   `A'` and have exact common-image intersection.
5. **Return to abstract structures.** Take `D` to be the finite Boolean
   algebra of subsets of the atoms of `D'`, with marking equal to the
   sum of the atom marks. Define
   `h_B(y)=prebananaBooleanMap(u,c_B(y))` and
   `h_C(z)=prebananaBooleanMap(v,c_C(z))`.
   The Boolean-operation, injectivity and parity lemmas for the codes
   and marked partition maps show these are embeddings in the original
   language. Naturality and the concrete commuting square give
   `h_B(f(x))=h_C(g(x))`.
6. **Exact intersection, with an explicit witness.** If
   `h_B(y)=h_C(z)`, the powerset intersection theorem supplies a
   common finite subset `r` of the source atom indices such that
   `prebananaBooleanMap(f',r)=c_B(y)` and
   `prebananaBooleanMap(g',r)=c_C(z)`. The element code `c_A` must be
   shown **surjective**, so choose `x∈A` with `c_A(x)=r`.
   Naturality then gives `c_B(f(x))=c_B(y)` and
   `c_C(g(x))=c_C(z)`. Injectivity of both codes yields
   `f(x)=y` and `g(x)=z`. Thus the images intersect exactly in
   their common copy of `A`.

Heredity and countability of the finite Boolean parity class, joint
embedding over the two-element Boolean algebra with zero marking,
and unbounded atom count are separate elementary finite-class facts.
Fraïssé's theorem then supplies the limit. For each fixed tuple
length `k`, the generated Boolean algebra has at most `2^k`
atoms, so there are only finitely many pointed finite generated
Boolean algebras together with their parity functions. Homogeneity
therefore gives finitely many automorphism orbits on `k`-tuples;
the usual Ryll–Nardzewski theorem supplies omega-categoricity.

## Lean coverage and strict gaps

- Merged: marked atom grid and powerset strong amalgamation (#100–#101);
  finite Boolean representation (#102); additive parity on the
  abstract atom set (#103, #106); finite object atom codes and parity
  (#108, #112); powerset partitions and abstract embeddings
  (#104–#105, #109); reindexing of marked fibres (#110).
- At the time of this note, draft #111 encodes arbitrary marked
  embeddings; draft #115 proves full Boolean-element naturality;
  draft #113 proves bijectivity of the element code (crucial for the
  witness `x` in step 6); draft #114 checks preservation of Boolean
  operations. None of these drafts should be called kernel-verified
  or merged until their dedicated proof and axiom checks pass.
- The final bundled abstract strong-amalgamation theorem, including
  the actual finite Boolean algebra target and original-language
  embeddings, is **not yet kernel-checked**. The manuscript
  proposition must retain a partial marker/TODO until then.
- The general Fraïssé existence and Ryll–Nardzewski implications are
  standard external theorems, not to be confused with the internal
  finite algebraic verification.

## Independent adversarial checks

Two independently formulated exhaustive finite checks were run:

- **34,361 compatible marked diagrams** with 1–3 source atoms and at
  most four atoms in each target. Checked even total target marking,
  both row and column parity marginals, nonempty projections, and
  exact intersection on every pair of Boolean-element subsets;
  **234,338 matching-pullback cases** were examined without a
  counterexample.
- **46,274 reindexing cases** (surjective atom partitions, independent
  permutations of source and target atom indices, and all Boolean
  subsets of the source) independently checked the element-map
  naturality identity.

These exhaustive checks do not prove the general theorem and cannot
replace the Lean kernel. They are valuable regressions and a check
against reversing the direction of atom partitions.

## Specific proof traps to guard against

- A Boolean embedding corresponds to a **surjection on target atoms
  towards source atoms**, never an injection in that direction.
- Global even marking alone is insufficient: **each individual source
  atom fibre** must have its prescribed parity.
- Equal embedded atoms are not the right intersection condition; the
  common-image statement quantifies over **all Boolean elements**.
- The exact intersection witness must be an actual element of
  `A`, obtained using surjectivity of the element code; leaving it
  as an arbitrary finite subset of source atoms is not yet the
  circulated proposition.
- The marked target and embeddings must live in the original
  Boolean-functional language with the parity predicate. The
  intermediate two-sided atom representation is an equivalence of
  presentations, not an enlargement of the finite class.
- The object nontriviality hypothesis `0 ≠ 1` is needed to ensure a
  positive number of atoms in the `Fin n` representation.
- Avoid upgrading the manuscript marker for omega-categoricity on
  the strength of finite amalgamation alone: the standard
  Fraïssé/homogeneity/oligomorphicity deduction must be cited or
  formalised separately.
