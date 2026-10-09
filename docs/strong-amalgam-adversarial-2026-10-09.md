# Strong BANANA amalgamation: independent proof architectures

**Status:** internal mathematical audit. The circulation manuscript is
frozen; this note does not authorise changes to its mathematical text.

## I. Circulation construction in split coordinates

An embedding of finite-dimensional vector spaces admits a linear
complement. After identifying the common source with the first
summand on both sides of each extension, we obtain finite coordinate
sets `L_A, R_A, U_B, V_B, U_C, V_C`. The two rectangular pairing
matrices `B,C` agree on `L_A × R_A`.

Form the left amalgam coordinates
`L_A ⊕ (U_B ⊕ U_C)` and the analogous right coordinates
`R_A ⊕ (V_B ⊕ V_C)`. Keep the two old submatrices and make the
unprescribed `U_B × V_C` and `U_C × V_B` blocks zero.

The old `BananaAmalgam.lean` file checked matrix restrictions,
injectivity of both coordinate inclusions and their *exact*
intersection. The new `BananaStrongBlockAmalgam.lean` turns
these restrictions into pairing-preserving embeddings on actual
finite coordinate vectors, and packages their intersection
as the strong amalgamation assertion for split diagrams.

This is precisely the finite matrix step of the circulated proof.
Transport to an arbitrary cospan is still an additional lemma.

## II. Adversarial alternative: a redundant-coordinate construction

There is a useful construction that avoids choosing complements as
*subspaces* and avoids a quotient pushout.

Let `f:A→B`, `g:A→C` be BANANA embeddings. Choose linear left
inverses of each component:
`p_{B,L} f_L = id`, `p_{C,L} g_L = id`, and the right-sort
counterparts. Such left inverses exist by finite-dimensional linear
algebra.

Take the new left sort to be `L_A ⊕ L_B ⊕ L_C`; take the right
sort to be `R_A ⊕ R_B ⊕ R_C`. With `-` denoting vector subtraction
(equal to addition over `F₂`), put
```
  j_B^L(b) = (p_{B,L} b, b - f_L(p_{B,L} b), 0),
  j_C^L(c) = (p_{C,L} c, 0, c - g_L(p_{C,L} c)),
```
and define `j_B^R,j_C^R` analogously.

For `x=(a,u,v)` and `y=(a',u',v')`, define
```
  β_D(x,y) =
       β_B(f_L(a) + u, f_R(a') + u')
     + β_C(g_L(a) + v, g_R(a') + v')
     - β_A(a,a').
```
This is bilinear. To check the restriction to B, note that the
B-part of `j_B(b)` is `b`, whereas its C-part is `g(p_B b)`.
Consequently the C-term equals
`β_A(p_{B,L} b,p_{B,R} b')` and cancels the final A-term.
Thus `β_D(j_B b,j_B b')=β_B(b,b')`; the C case is symmetric.

The images meet *only* in the common source: if
`j_B^L(b)=j_C^L(c)`, the second and third components force
`b=f_L(p_{B,L}b)` and `c=g_L(p_{C,L}c)`; equality of the first
components gives a common `a`. The same calculation holds on
the right sort. Moreover `j_B∘f=j_C∘g`, componentwise.

**Adversarial checks:**  The argument does not require the
pairings to be nondegenerate, nor does it require the retractions
to preserve the pairing; cancellation uses only preservation by
`f,g`. Neither a quotient nor any classification of quadratic
forms is used. The larger ambient dimension is harmless for
strong amalgamation.

This provides a promising *alternative Lean formalisation* of
arbitrary diagrams. It would require building a finite matrix
for the three-term pullback bilinear form and packaging the
four linear left inverses. The existing mathlib lemma
`LinearMap.exists_leftInverse_of_injective` supplies those
retractions (after rewriting injectivity as zero kernel).

## III. Scope of the circulation proposition

A full Lean verification of `prop:fraisse` has additional parts:

1. Strong amalgamation for **arbitrary embeddings**, not merely the
   split-coordinate diagram.
2. Joint embedding and hereditary closure.
3. Identification of the explicit finite-support pairing on
   countably many coordinates with the Fraïssé limit: age,
   universality, homogeneity and the extension property.
4. Local finiteness and oligomorphicity/`ω`-categoricity.

The proof of the perfect-pair homogeneity lemma is separately
kernel-checked. It can be reused for step 3. Do not label the whole
proposition green based solely on the matrix amalgamation lemma.

Independent adversarial referee agents are not currently available
through the connected tools; the two proof architectures and their
counterexample checks here are a desk audit, not separate referees.
