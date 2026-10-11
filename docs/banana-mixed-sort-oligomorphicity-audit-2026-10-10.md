# BANANA mixed-sort tuple orbits — adversarial audit

Date: 10 October 2026. This is an internal review of
`BananaLimitMixedTupleOrbits.lean`. It is **not** a report from an
independently spawned referee. Do not promote its declarations to
circulation validation markers before a successful Lean kernel and
transitive axiom audit.

## Exact scope

The explicit BANANA model has two distinct vector-space sorts
`V_L = ℚ →₀ F₂` and `V_R = ℚ →₀ F₂`, with the pairing
`β(x,y)=∑_q x(q)y(q)`. An ordinary tuple in the two-sorted
language can contain entries from the two sorts in an arbitrary
order. We model it as

```
  Fin n → Sum BananaLimitVector BananaLimitVector.
```

The tag distinguishes the two copies of the zero vector as well
as nonzero entries. This distinction is essential; replacing a
tagged zero by an untyped zero would collapse logically different
tuples.

## Adversarial proof audit A: finite invariant and completeness

For each tuple `t`, record its Boolean sort pattern `σ_t`,
its left-masked tuple `a_t` (zero in right positions), and its
right-masked tuple `b_t` (zero in left positions). The signature is

```
  (σ_t, bananaLimitTupleSignature a_t b_t).
```

For fixed `n`, this is finite: the pattern has `2^n` values,
the two kernel predicates are Boolean-valued functions on the
finite coefficient spaces `F₂^n`, and the pairing table has
`n²` binary entries.

Suppose signatures of `s,t` agree. The previously kernel-checked
tuple-signature completeness theorem supplies one **global** pair
of linear equivalences `(E_L,E_R)` preserving β and mapping all
left-mask entries and all right-mask entries coordinatewise.
Equality of the sort patterns prevents a left entry of `s`
from being matched to a right entry of `t`, or conversely.
For a left entry, the left-mask equality gives its exact image;
for a right entry, the right-mask equality does the same.
Consequently the same global automorphism maps the whole
tagged tuple `s` to `t`.

**Counterexample attempted:** If the sort pattern is omitted,
one-term tuples `[inl 0]` and `[inr 0]` have identical masked
vectors and kernel/pairing data but are never in the same orbit,
since a two-sorted automorphism preserves sorts. The new
signature retains the pattern, so it avoids this failure.

## Adversarial proof audit B: finite-orbit counting

The generic theorem `exists_finite_representatives_of_invariant`
does not require explicitly choosing or quotienting by the full
infinite automorphism group. It chooses one actual tuple from
each *realisable* finite signature and proves that every tuple
lies in the global orbit of one of these choices. This is
a finite set of orbit representatives, not merely a finite
number of formal signatures with no witnesses.

The proof is valid at `n=0`, for tuples in only one sort,
and for tuples containing repeated vectors or zeros.

## Independent small-model regression (not a Lean proof)

`scripts/check_banana_mixed_tuples.py` exhaustively enumerates
the full `GL(d,2)` action on standard finite perfect pairings
`F₂^d × F₂^d`, with contragredient action on the right sort.
For each tagged tuple it computes the mixed finite signature
and its **actual orbit** under every available perfect-pair
automorphism. It checks both directions: equal signatures have
the same orbit, and equal orbits have the same signature.

The locally executed script passed **9,150 tagged tuples**
over dimensions 0–3 (tuple lengths up to 4 in dimension 2),
including 168 automorphisms in dimension 3. This is useful
adversarial evidence and checks the subtle zero-sort corner
case, but it does not prove the countable-limit theorem.

## What the result establishes, and what it does not

Assuming the root Lean build and `#print axioms` checks pass,
we have the **usual mixed-sort formulation of oligomorphicity**:
for every `n`, the automorphism group of the explicit BANANA
pairing has finitely many orbits on ordered tagged `n`-tuples.

The standard Engeler–Ryll-Nardzewski–Svenonius theorem then
implies `ω`-categoricity of the countable first-order
two-sorted structure. The *general model-theoretic implication*
and the translation of the coordinate structure into Mathlib's
bundled `FirstOrder.Language.Structure` have **not** been
formalised in Lean, and this file does not claim otherwise.

A future model-theoretic Lean formalisation should explicitly
handle two-sorted coding, addition/zero on both sorts and the
binary `E` relation. No change to the frozen circulation
mathematical prose is authorised by this audit.
