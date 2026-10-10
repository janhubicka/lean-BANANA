import BANANA.NonPrecompact.BananaFinitePartialSystems

/-!
# Cofinal transfer of JEP and WAP for finite BANANA n-systems

The Kechris--Rosendal criterion is applied to the full class of finite
systems of partial automorphisms. The manuscript first finds a cofinal
subclass of perfect total systems and proves amalgamation there.

This file isolates the general transfer: cofinal JEP implies JEP,
and amalgamation in a cofinal subclass implies WAP in the ambient
class. All embeddings carry the prescribed source maps, so the proof
does not silently drop the partial-automorphism compatibility.

The hypotheses about perfect total systems are *not* discharged here.
In particular, the arbitrary orthogonal-diagram amalgamation needed
for this instance remains a separate formalisation obligation.
-/

namespace SuccessorTree.NonPrecompact

/-- Agreement of two n-system embeddings on the underlying carrier.
Agreement of the induced source maps follows from injectivity of
the domain embeddings (proved below). -/
def bananaSystemEmbeddingsAgree {n : ℕ}
    {S T : BananaFinitePartialSystem n}
    (f g : BananaFinitePartialSystemEmbedding S T) : Prop :=
  (∀ x, f.carrier.left x = g.carrier.left x) ∧
  (∀ y, f.carrier.right y = g.carrier.right y)

/-- Agreement on the carrier entails agreement of the map on the
source of each named partial automorphism, on both sorts. -/
theorem bananaSystemEmbeddingsAgree_sources {n : ℕ}
    {S T : BananaFinitePartialSystem n}
    (f g : BananaFinitePartialSystemEmbedding S T)
    (h : bananaSystemEmbeddingsAgree f g) :
    (∀ i (x : Fin (S.sourceLeftDim i) → F2),
      (f.source i).left x = (g.source i).left x) ∧
    (∀ i (y : Fin (S.sourceRightDim i) → F2),
      (f.source i).right y = (g.source i).right y) := by
  constructor
  · intro i x
    apply (T.domain i).left_injective
    calc
      (T.domain i).left ((f.source i).left x) =
          f.carrier.left ((S.domain i).left x) :=
        (f.domain_left i x).symm
      _ = g.carrier.left ((S.domain i).left x) :=
        h.1 ((S.domain i).left x)
      _ = (T.domain i).left ((g.source i).left x) :=
        g.domain_left i x
  · intro i y
    apply (T.domain i).right_injective
    calc
      (T.domain i).right ((f.source i).right y) =
          f.carrier.right ((S.domain i).right y) :=
        (f.domain_right i y).symm
      _ = g.carrier.right ((S.domain i).right y) :=
        h.2 ((S.domain i).right y)
      _ = (T.domain i).right ((g.source i).right y) :=
        g.domain_right i y

/-- Joint embedding for the full class of finite n-systems. -/
def BananaFiniteSystemsJEP (n : ℕ) : Prop :=
  ∀ S T : BananaFinitePartialSystem n,
    ∃ U : BananaFinitePartialSystem n,
      Nonempty (BananaFinitePartialSystemEmbedding S U) ∧
      Nonempty (BananaFinitePartialSystemEmbedding T U)

/-- Weak amalgamation: after extending S to S', every pair of
embeddings of S' can be amalgamated with agreement on S.
Equality is checked on both underlying sorts and automatically
entails agreement of the labelled partial maps. -/
def BananaFiniteSystemsWAP (n : ℕ) : Prop :=
  ∀ S : BananaFinitePartialSystem n,
    ∃ S' : BananaFinitePartialSystem n,
    ∃ e : BananaFinitePartialSystemEmbedding S S',
      ∀ (U V : BananaFinitePartialSystem n)
        (f : BananaFinitePartialSystemEmbedding S' U)
        (g : BananaFinitePartialSystemEmbedding S' V),
        ∃ W : BananaFinitePartialSystem n,
        ∃ h : BananaFinitePartialSystemEmbedding U W,
        ∃ k : BananaFinitePartialSystemEmbedding V W,
          bananaSystemEmbeddingsAgree
            ((h.comp f).comp e) ((k.comp g).comp e)

/-- A predicate on systems is cofinal when every system embeds
into a system satisfying that predicate. -/
def BananaFiniteSystemsCofinal {n : ℕ}
    (Good : BananaFinitePartialSystem n → Prop) : Prop :=
  ∀ S : BananaFinitePartialSystem n,
    ∃ T : BananaFinitePartialSystem n,
      Good T ∧ Nonempty (BananaFinitePartialSystemEmbedding S T)

/-- Joint embedding inside a specified subclass. -/
def BananaFiniteGoodSystemsJEP {n : ℕ}
    (Good : BananaFinitePartialSystem n → Prop) : Prop :=
  ∀ S T : BananaFinitePartialSystem n,
    Good S → Good T →
      ∃ U : BananaFinitePartialSystem n,
        Good U ∧
        Nonempty (BananaFinitePartialSystemEmbedding S U) ∧
        Nonempty (BananaFinitePartialSystemEmbedding T U)

/-- Amalgamation inside a specified subclass: all three inputs
are good, and the amalgam can also be taken good. -/
def BananaFiniteGoodSystemsAP {n : ℕ}
    (Good : BananaFinitePartialSystem n → Prop) : Prop :=
  ∀ (S T U : BananaFinitePartialSystem n),
    Good S → Good T → Good U →
    ∀ (f : BananaFinitePartialSystemEmbedding S T)
      (g : BananaFinitePartialSystemEmbedding S U),
      ∃ V : BananaFinitePartialSystem n,
        Good V ∧
        ∃ h : BananaFinitePartialSystemEmbedding T V,
        ∃ k : BananaFinitePartialSystemEmbedding U V,
          bananaSystemEmbeddingsAgree (h.comp f) (k.comp g)

/-- Joint embedding transfers from a cofinal subclass without
any closure assumption on that subclass. -/
theorem bananaFiniteSystems_jep_of_cofinal
    {n : ℕ} (Good : BananaFinitePartialSystem n → Prop)
    (hcofinal : BananaFiniteSystemsCofinal Good)
    (hjep : BananaFiniteGoodSystemsJEP Good) :
    BananaFiniteSystemsJEP n := by
  intro S T
  obtain ⟨S', hS', ⟨eS⟩⟩ := hcofinal S
  obtain ⟨T', hT', ⟨eT⟩⟩ := hcofinal T
  obtain ⟨U, _, ⟨p⟩, ⟨q⟩⟩ := hjep S' T' hS' hT'
  exact ⟨U, ⟨p.comp eS⟩, ⟨q.comp eT⟩⟩

/-- Cofinal amalgamation implies weak amalgamation of all
finite n-systems. The agreement maps retain the original
domain/range compatibility on both sorts. -/
theorem bananaFiniteSystems_wap_of_cofinal_amalgamation
    {n : ℕ} (Good : BananaFinitePartialSystem n → Prop)
    (hcofinal : BananaFiniteSystemsCofinal Good)
    (hap : BananaFiniteGoodSystemsAP Good) :
    BananaFiniteSystemsWAP n := by
  intro S
  obtain ⟨S', hS', ⟨e⟩⟩ := hcofinal S
  refine ⟨S', e, ?_⟩
  intro U V f g
  obtain ⟨U', hU', ⟨u⟩⟩ := hcofinal U
  obtain ⟨V', hV', ⟨v⟩⟩ := hcofinal V
  obtain ⟨W, _, h, k, hagree⟩ :=
    hap S' U' V' hS' hU' hV' (u.comp f) (v.comp g)
  refine ⟨W, h.comp u, k.comp v, ?_⟩
  constructor
  · intro x
    exact hagree.1 (e.carrier.left x)
  · intro y
    exact hagree.2 (e.carrier.right y)

end SuccessorTree.NonPrecompact
