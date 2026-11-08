# Track C — intrinsic generated units and native finite pairing bridge
## Internal adversarial handover, 8 November 2026

**Source-only, NOT a Lean verification certificate.** No circulation
TeX, appendix, existing TODO or validation marker has changed.

### Concrete Track B / Track C mismatch corrected

Track B's native finite heredity theorem takes
NonUnitalSubring R with an ambient BooleanRing R, which has a
multiplicative identity. The intended countable Folkman Fraïssé
limit has only the non-unital operations, so it is incorrect to
invoke that heredity theorem on a subring of the infinite ambient
limit directly. No global unit may be assumed.

A finite-stage tuple witness w supplies an isomorphism from the
non-unital generated subring of a finite atom-coded Boolean ring
to the *actual* generated subring of the ambient non-unital ring.
Inside the finite atom ring, Track B's intrinsic-unit
construction equips the finite generated subring with a local
BooleanRing. Transport that structure along w.left_generatedEquiv
or w.right_generatedEquiv. The target's new one is the image of
the source's intrinsic one; its inherited addition and multiplication
are exactly the original ambient non-unital operations.

The generic source-level constructor
folkmanBooleanRingOfNonUnitalEquiv does this without installing
a global typeclass instance on the ambient limit. The theorem
folkmanBooleanRingOfNonUnitalEquiv_unit_unique proves that
two finite-stage presentations yield the same intrinsic identity:
a left identity e and right identity f in the same fixed
multiplication satisfy e = ef = f. This gives choice independence
of the local unit, even though the ambient structure has no one.

### The actual ambient pairing on generated substructures

The finite-stage atlas by itself records full pairing
reconstruction but did not expose that the original ambient
pairing is additive. A finite Folkman code A is already realised
by an additive finite F₂ pairing on the entire Boolean rings:
folkmanNativeCodeRealisation A (merged Track B source).
FolkmanDirectedFinitePairingLaws.lean identifies that finite
pairing with the restriction of the ORIGINAL ambient β to a stage.
Cover two left and one right element in a common stage to obtain
β(x+x',y)=β(x,y)+β(x',y), and analogously cover one left and
two right elements for right additivity. These are statements
about all original elements, not only their atom code.

FolkmanAmbientGeneratedNativePairing.lean then equips each
actual finite generated two-sort substructure with its original
β restricted to the two intrinsically unital finite generated
subrings. This constructs a genuine FolkmanNativeFinitePairing
object with unchanged underlying non-unital operations.
Its generatedNativeCode_exists theorem applies the merged
Track B finite native representation theorem to obtain
a faithful finite atom-code isomorphism for this ACTUAL
generated pairing (including all β values).

The last statement is an important prerequisite for building
an initial finite paired bridge representing any specified
generated two-sort isomorphism. It is not itself a construction
of that initial bridge.

### Independently calculated finite semantic checks

Both deterministic regression scripts were run in the local
Python environment. They include source/target zero rings,
unowned atoms and empty generator tuples:

* check_folkman_intrinsic_units.py: 161 injective partial-owner
  maps, 9,208 generated tuple cases, 312,530 operation
  assertions. 525 generated zero-subring cases; 6,671 cases
  where the generated target identity differs from the ambient
  unit. The image of the source intrinsic identity always
  equals the intrinsic identity of the image generated ring.
* check_folkman_generated_native_pairing.py: 2,940 generated
  two-sort substructure cases, 46,366 explicit left/right
  pairing additivity assertions, 2,497 cases with a zero
  generated sort and 2,382 with an unowned ambient atom.

Both scripts refuse Python -O rather than silently disabling
their assertions. They are semantic tests only, not Lean proofs
or independently spawned model referees. The second regression
initially had an incorrect *expected sample count* (3,750
instead of 2,940); its expected count was corrected and the
exact corrected regression passed locally. No mathematical
identity failed.

### Dependency reconciliation

Track B PRs #305 and #309 were merged into main. Draft Track C
had not incorporated those files, and an exact-head build would
have immediately failed on missing imports. We used GitHub's
server-resolved PR test merge trees with strict parent SHA
checks to create TWO ordinary fast-forward merge commits
on the Track C branch: first the known Track B main snapshot
(23a6d1a), then the newer main snapshot (5a8467e).
The second draft branch merge head is 58584b48b143eb60.
Both old heads were protected by compare-and-swap leases;
no force update or merge of PR #308 INTO main occurred.

The merged branch contains the native finite heredity and
finite code realisation files, plus all Track C source.
GitHub's test merge trees preserved all main-only and
Track C-only file blobs. The root import graph reaches
the new axiom-audit modules. Source-level inspection
finds no new admitted proof declarations and the PR diff
contains no TeX/BibTeX changes.

### Remaining tasks for genuine Track C completion

1. Run the exact-head PINNED local Lean build, including the
   new intrinsic-unit, ambient pairing, and generated native
   pairing modules. Inspect every transitive #print axioms
   report and repair any real elaboration errors. The current
   runtime has no lean/lake/elan binary and local DNS for
   github.com is unavailable; no CI runners were dispatched.
2. Construct the countable homogeneous two-sorted Folkman limit
   in the original non-unital signature, or invoke a separately
   verified general Fraïssé existence theorem. Pinned Mathlib's
   Fraisse.lean explicitly lists existence as a TODO.
3. Using the newly packaged native finite generated objects,
   build the initial paired bridge for each actual generated
   isomorphism; verify its target/source code pairing and
   the original labelled generator maps.
4. Establish all four one-point extensions of paired bridges
   from the genuine limit's finite embedding extension
   property and the native finite strong amalgamation theorem.
5. Use the existing cofinal bridge, global automorphism,
   profile iff-orbit, and finite mixed-sort orbit theorems.
   Ryll–Nardzewski is an external standard consequence.
6. Obtain genuinely independent adversarial referees for
   both exact Lean statement fidelity and the mathematical
   Fraïssé/back-and-forth proof. No such agent could be
   spawned in this runtime.

**PR #308 remains draft and unmerged. Do not advance circulation
validation markers merely because source-level tests pass.**
