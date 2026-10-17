import BANANA.NonPrecompact.PrebananaFiniteBridgeLimitBijection

/-!
# From exhaustive finite bridges to a global marked Boolean automorphism

An exhaustive increasing sequence of finite bridges gives a coherent
bijection between its two countable ambient models. Its values are
defined by any finite representative. Because all the finite left
and right maps preserve joins, the bijection preserves joins too.

A bijective join-preserving map between Boolean algebras is an order
isomorphism, and therefore preserves the whole Boolean algebra
language. The bridge map also preserves the unary F₂ marking.

Applying the two-sided cofinal bridge theorem starting from an
arbitrary finite bridge produces a global marking-preserving
Boolean automorphism extending the prescribed finite marked map.
No model-theoretic homogeneity premise is used.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Coherence plus the finite Boolean homomorphism laws imply
preservation of joins by the global bridge map. -/
theorem PrebananaFiniteBridge.forward_map_sup
    {M : PrebananaCountableBooleanModel}
    (chain : ℕ → PrebananaFiniteBridge M)
    (hmono : Monotone chain)
    (hleft : ∀ x : M.carrier, ∃ n : ℕ,
      ∃ a : (chain n).base.carrier, (chain n).left.hom a = x)
    (x y : M.carrier) :
    PrebananaFiniteBridge.forward chain hleft (x ⊔ y) =
      PrebananaFiniteBridge.forward chain hleft x ⊔
      PrebananaFiniteBridge.forward chain hleft y := by
  let c := PrebananaFiniteBridge.chooseLeft chain hleft x
  let d := PrebananaFiniteBridge.chooseLeft chain hleft y
  have hc : (chain c.1).left.hom c.2 = x :=
    PrebananaFiniteBridge.chooseLeft_spec chain hleft x
  have hd : (chain d.1).left.hom d.2 = y :=
    PrebananaFiniteBridge.chooseLeft_spec chain hleft y
  let N := max c.1 d.1
  obtain ⟨f, hfL, hfR⟩ : chain c.1 ≤ chain N :=
    hmono (le_max_left c.1 d.1)
  obtain ⟨g, hgL, hgR⟩ : chain d.1 ≤ chain N :=
    hmono (le_max_right c.1 d.1)
  let z : (chain N).base.carrier := f.hom c.2 ⊔ g.hom d.2
  have hz : (chain N).left.hom z = x ⊔ y := by
    change (chain N).left.hom (f.hom c.2 ⊔ g.hom d.2) = x ⊔ y
    rw [map_sup (chain N).left.hom, hfL c.2, hgL d.2, hc, hd]
  have hcx :
      PrebananaFiniteBridge.forward chain hleft x =
      (chain c.1).right.hom c.2 := rfl
  have hdy :
      PrebananaFiniteBridge.forward chain hleft y =
      (chain d.1).right.hom d.2 := rfl
  calc
    PrebananaFiniteBridge.forward chain hleft (x ⊔ y) =
        PrebananaFiniteBridge.forward chain hleft
          ((chain N).left.hom z) :=
        congrArg (PrebananaFiniteBridge.forward chain hleft) hz.symm
    _ = (chain N).right.hom z :=
      PrebananaFiniteBridge.forward_of_left chain hmono hleft N z
    _ = (chain c.1).right.hom c.2 ⊔
        (chain d.1).right.hom d.2 := by
          change (chain N).right.hom (f.hom c.2 ⊔ g.hom d.2) = _
          rw [map_sup (chain N).right.hom, hfR c.2, hgR d.2]
    _ = PrebananaFiniteBridge.forward chain hleft x ⊔
        PrebananaFiniteBridge.forward chain hleft y := by
          rw [hcx, hdy]

/-- A two-sided exhaustive bridge chain yields an order isomorphism
of the ambient Boolean algebra (hence a genuine Boolean automorphism). -/
noncomputable def PrebananaFiniteBridge.limitOrderIso
    {M : PrebananaCountableBooleanModel}
    (chain : ℕ → PrebananaFiniteBridge M)
    (hmono : Monotone chain)
    (hleft : ∀ x : M.carrier, ∃ n : ℕ,
      ∃ a : (chain n).base.carrier, (chain n).left.hom a = x)
    (hright : ∀ x : M.carrier, ∃ n : ℕ,
      ∃ a : (chain n).base.carrier, (chain n).right.hom a = x) :
    M.carrier ≃o M.carrier where
  toEquiv := PrebananaFiniteBridge.limitEquiv chain hmono hleft hright
  map_rel_iff' := by
    intro x y
    have hsup :=
      PrebananaFiniteBridge.forward_map_sup chain hmono hleft x y
    constructor
    · intro hxy
      have heq : x ⊔ y = y := sup_eq_right.mpr hxy
      have hmaps :
          PrebananaFiniteBridge.forward chain hleft x ⊔
            PrebananaFiniteBridge.forward chain hleft y =
          PrebananaFiniteBridge.forward chain hleft y := by
        rw [← hsup, heq]
      exact sup_eq_right.mp hmaps
    · intro hxy
      have heq :
          PrebananaFiniteBridge.forward chain hleft x ⊔
            PrebananaFiniteBridge.forward chain hleft y =
          PrebananaFiniteBridge.forward chain hleft y :=
        sup_eq_right.mpr hxy
      have hinj : Function.Injective
          (PrebananaFiniteBridge.forward chain hleft) :=
        (PrebananaFiniteBridge.limitEquiv chain hmono hleft hright).injective
      have hxy' : x ⊔ y = y := by
        apply hinj
        rw [hsup]
        exact heq
      exact sup_eq_right.mp hxy'

/-- Back-and-forth yields an order automorphism of any countable
marked Boolean algebra satisfying finite ambient subalgebras and
the unconditional finite marked extension property. It extends
both embeddings of an arbitrary prescribed finite bridge. -/
theorem PrebananaFiniteBridge.exists_global_marked_automorphism
    {M : PrebananaCountableBooleanModel}
    (hfinite : M.HasFiniteAmbients)
    (hext : M.HasFiniteExtensionProperty)
    (p : PrebananaFiniteBridge M) :
    ∃ E : M.carrier ≃o M.carrier,
      (∀ x : M.carrier, M.μ (E x) = M.μ x) ∧
      ∀ a : p.base.carrier, E (p.left.hom a) = p.right.hom a := by
  classical
  obtain ⟨chain, hfirst, hmono, hleft, hright⟩ :=
    PrebananaFiniteBridge.exists_exhaustive_chain hfinite hext p
  let E : M.carrier ≃o M.carrier :=
    PrebananaFiniteBridge.limitOrderIso chain hmono hleft hright
  refine ⟨E, ?_, ?_⟩
  · intro x
    exact PrebananaFiniteBridge.limitEquiv_preserves_mark
      chain hmono hleft hright x
  · intro a
    have hp : p ≤ chain 0 := le_of_eq hfirst.symm
    obtain ⟨f, hfL, hfR⟩ := hp
    calc
      E (p.left.hom a) =
        E ((chain 0).left.hom (f.hom a)) :=
          congrArg E (hfL a).symm
      _ = (chain 0).right.hom (f.hom a) :=
        PrebananaFiniteBridge.forward_of_left
          chain hmono hleft 0 (f.hom a)
      _ = p.right.hom a := hfR a

end SuccessorTree.NonPrecompact
