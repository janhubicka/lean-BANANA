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
