# Pre-BANANA: explicit five-ary Fraïssé limit — formalisation plan

Status: **mathematical construction and finite adversarial audit**, **not yet
formalised in Lean**. This note belongs to the Lean development, not to the
frozen circulation text. Existing Lean proofs of finite strong amalgamation,
joint embedding, finite atom presentations, generated Boolean subalgebras and
conditional invariant-mass obstruction should be reused.

## Aim

Construct the countable Fraïssé limit of the class of nontrivial finite
Boolean algebras with an additive marking
\(\mu:B\to\mathbb F_2\), satisfying \(\mu(0)=\mu(1)=0\).
An embedding is a unital Boolean embedding preserving \(\mu\).

The Mathlib file `Mathlib/ModelTheory/Fraisse.lean` contains the language of
ages, countable-age existence, direct limits, extension pairs and
ultrahomogeneity, but explicitly lists *existence of Fraïssé limits* as a
TODO. In particular, countable age alone does not give the requisite
ultrahomogeneity. A direct construction below avoids assuming that
missing theorem.

## A fixed tower

Let \(W_n=\{0,1,2,3,4\}^{n}\). Set
\(B_n=\mathcal P(W_n)\); its atoms are the singleton words.
Define an atom marking \(m_n:W_n\to\mathbb F_2\) recursively:

* \(m_0(\varnothing)=0\);
* for \(w\in W_n\), set
  \(m_{n+1}(w0)=m_{n+1}(w1)=0\),
  \(m_{n+1}(w2)=m_{n+1}(w3)=1\), and
  \(m_{n+1}(w4)=m_n(w)\).

Extend the marking to subsets by addition:
\[
  \mu_n(X)=\sum_{w\in X}m_n(w).
\]
Define \(i_n:B_n\hookrightarrow B_{n+1}\) by inverse image of the
prefix map \(W_{n+1}\to W_n\).

**Compatibility.** Every parent has child-mark sum
\(0+0+1+1+m_n(w)=m_n(w)\) in \(\mathbb F_2\). Thus
\(i_n\) is injective and preserves all Boolean operations and \(\mu\).
Since \(\mu_0(1)=0\), all \(\mu_n(1)=0\).
Every \(B_n\) is a pre-BANANA model.

**Rich descendants.** If \(w\) has mark \(p\in\{0,1\}\), then at depth
\(k\) below it the numbers of descendants of marks \(1\) and \(0\) are
respectively
\[
  M_k(p)=\frac{5^k-1}{2}+p,\qquad
  Z_k(p)=\frac{5^k+1}{2}-p.
\]
Indeed \(M_0(p)=p\) and \(M_{k+1}(p)=2\cdot5^k+M_k(p)\).
Both numbers tend to infinity, uniformly in \(p\).
Also \(M_k(p)\equiv p\bmod 2\), since \(5^k\equiv1\bmod4\).

## Finite-extension property (key lemma)

**Claim.** Given finite marked Boolean algebras \(A,B\), embeddings
\(f:A\hookrightarrow B\) and \(e:A\hookrightarrow B_n\), there are
\(k\ge 0\) and an embedding \(g:B\hookrightarrow B_{n+k}\) such that
\[
  g\circ f=i_{n,n+k}\circ e.
\]

Proof. Each source atom \(a\in\operatorname{At}(A)\) determines a
nonempty set \(E_a\subseteq W_n\) of ambient atoms beneath \(e(a)\).
The atoms of \(B\) beneath \(f(a)\) form a nonempty finite set \(F_a\).
Compatibility of markings implies
\[
 \sum_{w\in E_a}m_n(w)
   =\mu_A(a)
   =\sum_{b\in F_a}\mu_B(b).
\]

In fact we may choose the **uniform depth**
\(k=\#\operatorname{At}(B)\), independent of \(n\), \(e\), and the
sizes of the source atom fibres. From \(M_0(p)=p\geq0\) and
\(M_{k+1}(p)=M_k(p)+2\cdot5^k\), induction gives
\(M_k(p)\geq2k\); also \(Z_k(p)=M_k(1-p)\geq2k\).
Each \(E_a\) is nonempty, so its descendants at depth \(k\) contain
at least \(2k\) marked and \(2k\) unmarked atoms. This exceeds
each of the two required numbers
\(\#\{b\in F_a:\mu_B(b)=0\}\) and
\(\#\{b\in F_a:\mu_B(b)=1\}\), both at most \(k\).
Thus one explicit common depth works for every source fibre.

For each \(b\in F_a\), put one distinct descendant of mark
\(\mu_B(b)\) into a bin \(P_b\). The as-yet unallocated descendants
have total mark \(0\): their mark sum is
\(\mu_A(a)-\sum_{b\in F_a}\mu_B(b)=0\).
Put **all** of these remaining descendants into any one of the
nonempty bins. Every \(P_b\) remains nonempty and has mark
\(\mu_B(b)\). This constructs a partition of \(W_{n+k}\) into
nonempty bins labelled by atoms \(b\) of \(B\).
Its inverse-image Boolean map is a marking-preserving embedding
\(g\). For an atom \(a\) of \(A\), the union of bins labelled by
\(F_a\) is exactly the set of descendants of \(E_a\), giving the
required commuting square. Equality on all elements follows from
Boolean additivity. \(\square\)

The **residual parity step** is essential: it is not enough merely
to assign one leaf of the prescribed mark to each new atom. The
remaining leaves must be placed without changing that parity.

## The limit and its properties

Form the increasing union (or directed limit) \(M=\bigcup_n B_n\)
along the injective maps \(i_n\), transporting Boolean operations
and marking through compatible stages.

1. \(M\) is countably infinite and locally finite.
2. Every finitely generated Boolean subalgebra of \(M\) is contained
   in some \(B_n\) and is a finite marked Boolean algebra.
3. Every finite marked Boolean algebra embeds into \(M\): use the
   extension property over the two-element algebra with zero mark.
4. Every finite extension diagram over a finite subalgebra of \(M\)
   embeds back into \(M\) over its base, by factoring that base through
   some \(B_n\) and applying the finite-extension lemma.
5. Back-and-forth over enumerations of the countable \(M\) therefore
   extends every isomorphism of finite marked subalgebras to an
   automorphism. Thus \(M\) is ultrahomogeneous and has exactly the
   intended finite age.
6. An \(r\)-tuple generates a Boolean algebra with at most \(2^r\)
   atoms. Only finitely many such marked algebras with distinguished
   generators exist up to isomorphism; ultrahomogeneity gives finitely
   many tuple orbits and hence \(\omega\)-categoricity.

The measure obstruction already formalised in
`PrebananaHomogeneousLimitMassObstruction.lean` can then be applied
once the limit, automorphism group, Stone action, and relevant
invariant-measure interface have been constructed.

## Suggested Lean modules and exact milestones

1. **Finite embedding calculus**: identities and composition for
   `PrebananaFiniteBooleanEmbedding` (draft #193).
2. **Finite tower interface**: stages \(B_n\), embeddings \(i_n\),
   compatible iterated embeddings and marking preservation.
3. **Word-marking recursion and arithmetic**: prove parent/child sum,
   total top parity and both explicit descendant counts.
4. **Partition-realisation lemma**: formalise the residual-even-parity
   allocation argument for finite marked sets. This is the principal
   new combinatorial step.
5. **Finite extension**: prove the commuting-square embedding above.
6. **Limit and back-and-forth**: use Mathlib's directed-limit and
   extension-pair mechanisms where they fit, but prove all required
   language/embedding bridges; do not assert a generic Fraïssé-limit
   existence theorem that has not been proved.
7. **Topological dynamics**: formalise the Stone representation and
   invariant-measure transfer separately. Do not conflate conditional
   finite mass contradiction with the full non-amenability theorem.

Any new circulation TeX entries may be only `\todo` notes and
`\leanverified...` markers for **completed kernel checks**.

## Adversarial finite check

Independently of Lean, an exhaustive Python test enumerated all
\(1{,}022\) parity-compatible desired child-mark patterns of lengths
\(1\) through \(9\), for parent marks \(0,1\). For each pattern, it
selected the first descendant depth having enough leaves of each
mark, assigned one leaf to each child, allocated all leftovers to
one bin, and checked:

* the bins are nonempty and partition the full descendant set;
* the mark of each bin is exactly the prescribed mark;
* all parent/child parity constraints hold.

All tests passed; the maximum required depth was \(2\).
For levels \(k=1,\dots,4\), the observed \((Z_k,M_k)\) counts were
\((3,2),(13,12),(63,62),(313,312)\) for parent mark \(0\), and
the reversed pairs for parent mark \(1\).

A second independent exhaustive check covers **1,327 complete finite
extension diagrams**: one existing five-atom ambient stage, between
one and three source atoms, at most three target atoms, all surjective
atom partitions in the two embeddings and every parity-compatible
choice of target marking. It verifies the extension square, disjoint
nonempty bins, full coverage and correct mark of every bin, using
the uniform depth equal to the number of target atoms.

The complete reproducible check is
`scripts/check_prebanana_fiveary_extension_small.py`
(run `python3 scripts/check_prebanana_fiveary_extension_small.py`).

**Limitations:** This enumerative check is not a Lean proof and does
not verify direct-limit construction, countable homogeneity, the
Stone action, or topological non-amenability.
