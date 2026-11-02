# Track B continuation: native representatives and hereditary closure

Internal development note, 2 November 2026. **DRAFT / NOT KERNEL-VERIFIED.**

## Pinned starting point and scope

- Track B PR #309: `6c662eddc25fb9b0d6a4c091b61daeffe60b4a78`.
- Upstream native-index PR #305: `7928adf9c6749fe885c5a4f8be6b08a17fd89cfe`.
- Both were still open drafts when read for this continuation.
- Pinned successor dependency: `d9be105f73ca5a0f3f411b87d4c2419d0eb94753`.
- Its pinned mathlib: `5bd58ac291422a21f412ae354c91e7d172255a2c`.

Only Track B Lean source, its dedicated axiom audit, a regression and this
internal note are added. No manuscript, appendix, root `BANANA.lean`, shared
Track A API, Track C source or upstream PR #305 branch is modified.

## New native-object direction

`FolkmanNativeFiniteCodeRealisation.lean` supplies the previously missing
reverse direction from an atom code to an actual finite native object:

1. `FolkmanNativeCodeRing n` is `AsBoolRing (Finset (Fin n))`, with an
   explicit finite instance; `n = 0` includes the zero ring.
2. `folkmanNativeCodeRealisation A` gives these two rings the double-sum
   pairing of `A.edge`, with additivity proved in both coordinates.
3. `folkmanNativeFiniteCodeRingEquiv` upgrades the existing atom-support
   bijection to an actual ring isomorphism.
4. `folkmanNativeFiniteCodeIso` preserves the original cross-pairing on
   every pair of native ring elements.
5. `folkmanNativeFinite_countable_native_representatives` supplies a
   countably indexed family of *native* objects representing every native
   finite isomorphism type. The codes need not be unique or invariant under
   relabelling: no converse claim about equality of codes is made.
6. `folkmanNativeFinite_native_objects_unbounded` constructs native objects
   with more than any prescribed number of elements in each sort. It uses
   singleton injections, not merely a bound on a formal code parameter.

The accompanying `...AxiomAudit.lean` lists all new proof-bearing declarations.
All these claims are SOURCE IMPLEMENTATIONS, pending Lean elaboration.

`RingEquiv` is used only for object isomorphisms. This does not strengthen the
embedding convention to unital maps: a bijective multiplicative/additive map
between rings necessarily preserves their identities. General embeddings
remain `NonUnitalRingHom`, allowing private target atoms.

## Statement-fidelity finding: hereditary closure is not just pairing pullback

The existing `FolkmanNativeFinitePairing.pullback` assumes that its source
carriers already have `BooleanRing` instances. It proves restriction of the
pairing, but by itself does not construct the needed ring structure on an
arbitrary finite substructure closed under zero, addition and multiplication.

In particular, one must NOT use an ambient-unital subring notion. In the
powerset ring on two atoms, the subring `{empty, {first atom}}` is closed
under the named operations but excludes the ambient greatest element. Its
own identity is `{first atom}`. The zero subring must also be allowed.

The mathematical closure argument is straightforward: the union of all
members of a finite non-unital Boolean subring belongs to it, since union
is the term `(x + y) + x*y`; this finite union is its multiplicative identity.
To finish the native HP interface, formalise that construction (or the
corresponding finite atom-partition representation), then transport the
pairing restriction through it. No claim is made that the printed heredity
assertion is false. This is a formal-interface obligation, not an authorised
change to the frozen manuscript.

## Executed finite regressions

The already supplied strong-amalgamation script was run again locally:

- 841 two-sort diagrams;
- 34,403 compatible pairing systems, all extendible;
- 34,514 incompatible systems, all inconsistent.

The new `scripts/check_folkman_native_realisation_small.py` was executed:

- 689 atom-code objects, including both zero-ring sorts;
- 37,477 original/native pairing-value comparisons;
- 578,662 additivity equalities;
- 341 Boolean-tuple versus bit-mask ring-operation pairs;
- 231 arbitrary injective zero-preserving candidate functions;
- 29 genuine ring embeddings, including 17 non-unital ones;
- 82 comparisons of original maps with recovered owner-fibre maps;
- 75 finite closed subrings on ambient rings with at most four atoms,
  including 51 without the ambient unit, all having the expected own unit.

The map enumeration starts with arbitrary functions, NOT owner maps, so it
does not assume the representation it tests. The subring enumeration starts
with arbitrary subsets containing zero, NOT a preselected unital subclass.
These are exhaustive within the stated finite ranges, not proofs in Lean.

## Verification status and next gate

No Lean, Lake or Elan executable was present. Direct GitHub access from the
container failed DNS resolution, so the pinned toolchain could not be
installed there. GitHub Actions were not used. No independent model referee
could be launched with the available tools; the finite checks must not be
reported as independently spawned referees.

After validating upstream #305, run on the exact resulting Track B head:

```sh
python3 scripts/check_lean_module_graph.py
lake build BANANA.NonPrecompact.FolkmanNativeFiniteClassInterface
lake build BANANA.NonPrecompact.FolkmanNativeFiniteClassMorphismWitness
lake build BANANA.NonPrecompact.FolkmanNativeFiniteCodeRealisation
lake env lean BANANA/NonPrecompact/FolkmanNativeFiniteClassInterfaceAxiomAudit.lean
lake env lean BANANA/NonPrecompact/FolkmanNativeFiniteClassMorphismWitnessAxiomAudit.lean
lake env lean BANANA/NonPrecompact/FolkmanNativeFiniteCodeRealisationAxiomAudit.lean
lake build BANANA
bash scripts/audit_all_axioms_local.sh
python3 scripts/check_folkman_track_b_strong_ap_small.py
python3 scripts/check_folkman_native_realisation_small.py
```

Only `propext`, `Classical.choice` and `Quot.sound` are allowed as transitive
proof axioms. Independently audit the exact theorem statements, native
isomorphism conventions, zero rings, and hereditary carrier construction.

The explicit new module builds are essential: integration alone owns the
root imports, and `lake build BANANA` by itself is not a substitute for
checking a new module absent from that root.

Do not merge or advance any manuscript validation marker before these checks.
Full native class-level packaging, hereditary-carrier closure, the countable
homogeneous limit and genuine global automorphism orbits remain outstanding.
