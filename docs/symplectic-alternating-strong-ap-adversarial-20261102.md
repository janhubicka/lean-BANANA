# Independent adversarial audit — finite alternating-form amalgamation

**Date:** 2 November 2026
**Scope:** circulation symplectic application only; frozen TeX untouched
**Formal status:** DRAFT, not kernel-verified

## Statement fidelity

The circulation defines Ksp as the finite *nondegenerate* alternating
spaces and immediately speaks of the Fraïssé age and one-dimensional members.
This cannot literally be correct: a nondegenerate alternating space of
dimension two has one-dimensional degenerate subspaces. The nondegenerate
finite subclass is not hereditary and contains no one-dimensional members.

The appropriate hereditary class is **all** finite alternating bilinear
F2-spaces with arbitrary injective isometric embeddings. This is the age
of the countable orthogonal sum of hyperbolic planes. Nondegeneracy is
retained only in test target subspaces used for the residue-colouring lemma.
The manuscript already contains this issue as a TODO; do not change or
duplicate circulation prose or reintroduce an author-removed note.

## Two independent mathematical arguments

**A. Matrix amalgam.** Choose a common basis for the shared subspace A
and complementary bases X and Y in the two extensions. An alternating
matrix over F2 has zero diagonal and is symmetric; neither condition
alone is enough. The block matrix on A ⊕ X ⊕ Y agrees with B on
A ⊕ X, agrees with C on A ⊕ Y, and has zero X×Y and Y×X blocks.
Agreement on A×A ensures consistency. It is again alternating and
the two induced forms are preserved.

**B. Vector-space intersection, independently of matrix arithmetic.**
The left coordinate inclusion sends (a,x) to (a,x,0); the right sends
(a,y) to (a,0,y). Equality occurs iff x=y=0 and the A coordinates
agree. Hence the intersection of the two *vector-space images* is
exactly the embedded A, not merely an intersection of selected basis
indices. The new Lean module packages two F2-linear maps and
an existential common-vector intersection criterion.

The new certificate works in coordinate systems in which the common
subspace has already been identified. **Reduction of arbitrary injective
isometries to these shared coordinates still requires a basis-choice
argument in Lean.** Matrix restriction on basis coordinates also needs
to be connected to preservation of bilinear forms on all vectors in
the eventual arbitrary-embedding interface.

## Independent finite adversarial regression

The committed Python script check_symplectic_alternating_strong_ap_small.py
exhaustively enumerates alternating matrices, including degenerate and
odd-dimensional spaces, with common A and private dimensions A, X, Y
each from 0 through 2. Every compatible pair is amalgamated using the
zero-cross matrix.

Locally executed on 2 November 2026:
- 2,875 compatible alternating-form amalgams;
- 632,512 left original-vector pairing checks;
- 632,512 right original-vector pairing checks;
- 606,205 separate tests of equality of embedded left/right vectors
  iff both are the same vector of the common A.

All passed. The regression is neither an arbitrary-dimension proof
nor a Lean kernel certificate.

## Verification gate

Run locally on the **exact PR head** using the pinned Lean toolchain:

    lake build BANANA.NonPrecompact.SymplecticAlternatingStrongAmalgam
    lake env lean BANANA/NonPrecompact/SymplecticAlternatingStrongAmalgamAxiomAudit.lean
    python3 scripts/check_symplectic_alternating_strong_ap_small.py

Check that the proof uses only permitted underlying axioms and that
the theorem signature still allows degenerate matrices. Then prove
the arbitrary-isometry shared-basis reduction, establish the complete
hereditary/JEP/AP interface and verify the copy-degree propagation
lemma against this corrected class. The separate quadratic-residue
proof still has recorded corrections to polarisation and moment
divisibility; this PR does **not** close those issues. No GitHub
Actions runners and no unapproved manuscript prose edits.


## Continuation: full-vector preservation and coordinate changes

**Added 2 November 2026, draft only:** The separate modules
SymplecticAlternatingBilinPreservation.lean and
SymplecticAlternatingCoordinateTransport.lean propose proofs of
the remaining vector-level obligations.

The first gives the equalities

    D(incB(u), incB(v)) = B(u,v)
    D(incC(u), incC(v)) = C(u,v)

for all coordinate vectors u,v, not merely at basis entries. They
use the exact Mathlib primitive Matrix.toBilin'_apply from the
project's pinned Mathlib commit
5bd58ac291422a21f412ae354c91e7d172255a2c.
Its expression is the F2-double sum
sum_i sum_j u_i * matrix_ij * v_j. The inserted zero coordinates
annihilate all unwanted summands, and the source blocks of D recover
the source double sums.

**Independent derivation:** Every vector is an F2-linear combination
of basis vectors and a bilinear pairing is determined by its values
on pairs of basis vectors. Each source basis vector maps to its
corresponding coordinate basis vector in the amalgam. The previously
proved source-block matrix restrictions therefore imply the full-vector
equalities. This is independent of simplifying the double sum above.
Neither argument assumes nondegeneracy.

The second module handles arbitrary source carriers VB, VC and a
common VA, conditional on compatible F2-linear coordinate
equivalences eA, eB, eC. Given original embeddings iB:VA->VB and
iC:VA->VC, it requires

    eB(iB(a)) = (eA(a), 0)
    eC(iC(a)) = (eA(a), 0).

Composing eB and eC with the standard coordinate inclusions
produces linear maps fB and fC into the common amalgam. Their images
intersect precisely in pairs of the form (iB(a),iC(a)) for a in VA.
Both vector-pairing identities are transported.

### Independent change-of-basis adversary

A second reproducible local test, in
scripts/check_symplectic_alternating_basis_change_small.py, samples
53 random invertible basis changes for each triple of dimensions
A,X,Y at most 2 (seed 20261102). It checks the pulled-back forms
and source embeddings on all vectors. Results:

- 1,431 compatible configurations with random basis changes;
- 3,339 common-subspace embedding checks;
- 70,119 full-vector pairing checks on each side;
- 54,537 exact intersection comparisons.

All passed in the local Python runtime; these are tests, not a
Lean certificate.

### Remaining arbitrary-embedding bridge

For arbitrary injective isometries iB:A->B, iC:A->C of finite
alternating spaces, choose a basis a_i of A, extend its image
iB(a_i) to a basis of B, and independently extend iC(a_i) to
a basis of C. Since the embeddings preserve the pairing, their
A-by-A matrix blocks coincide. The resulting coordinate
equivalences satisfy the conditional theorem above.

This standard basis-extension step still requires an explicit Lean
theorem with the exact original finite-dimensional bilinear-form
carriers. A complete AmalgamationSystem instance for the imported
SuccessorTree/CopyRamsey.lean theorem is also pending. Neither new
draft module nor the finite tests warrants a green manuscript marker.

**Build gate:** locally run lake build on all three new Lean modules,
lake env lean on their axiom-audit files, and inspect exact theorem
types. Do not use GitHub Actions runners.


## Concrete Lean strategy for the final compatible-basis lemma

The pinned Mathlib code offers a route which does not require a
custom implementation of Gaussian elimination:

1. For any injective original linear map iB: VA -> VB, the range
   LinearMap.range iB is a submodule of VB. Use
   LinearEquiv.ofInjective to identify VA with that range.
2. Apply the verified Mathlib theorem
   Submodule.exists_isCompl to obtain a complementary submodule
   QB of VB. Its associated Submodule.prodEquivOfIsCompl gives
   a linear equivalence from the product of the image submodule
   and QB to VB. Repeat independently for VC.
3. Use a basis of VA and bases of the two complements to make
   coordinate equivalences to function spaces indexed by
   Sum A X and Sum A Y. Over finite-dimensional vector spaces,
   the basis-index types are finite. Mathlib offers
   Finsupp.linearEquivFunOnFinite and the standard
   basis coordinate equivalences for this final step.
4. By construction, both original embeddings of VA have
   identical A-block coordinates. Their bilinear matrices
   agree on A-by-A because the original embeddings are
   isometries, independently of degeneracy. Apply
   symplecticAlternating_strongAmalgam_of_compatibleCoordinates.

Important: the complement is a *vector-space* complement, not an
orthogonal complement. Requiring orthogonal complements could fail
when the common subform is degenerate. Avoid introducing
nondegeneracy in the Lean hypothesis while extracting this bridge.

The existence and composition of the requisite coordinate
equivalences are NOT yet kernel-checked in this PR. This note
is a concrete implementation plan with API names checked in
the pinned Mathlib source, not a claimed Lean proof.


### Counterexample to an orthogonal-complement shortcut

Let B be the two-dimensional hyperbolic plane with basis (e,f),
form B(e,f)=B(f,e)=1, and zero diagonal. Let A=span(e), which
carries the zero (degenerate) alternating form. A is a legitimate
one-dimensional member of the **corrected** hereditary class.
A is its own orthogonal complement in B:

    A^perp = {v : B(v,e)=0} = span(e) = A.

Consequently B is NOT A + A^perp, let alone their direct sum.
Any Lean theorem that silently asserts an orthogonal complement for
arbitrary A is false. The block construction uses an ordinary
vector-space complement span(f), and retains the nonzero
cross-pairings B(e,f) in its matrix. This demonstrates concretely
why the direct-sum proof of the perfect-total BANANA subsystem
amalgamation cannot be copied without modification to the
symplectic age containing degenerate subspaces.
