import BANANA.NonPrecompact.PrebananaFiniteBridgeCofinal

/-!
# The bijection obtained from an exhaustive chain of finite marked bridges

An increasing sequence of finite marked Boolean bridges determines
a map from the left countable ambient model to the right one: choose
a finite-stage representative of an element and apply the bridge's
right embedding. Coherence guarantees the answer is independent of
the representative.

When both bridge images exhaust the model, the map has an inverse,
obtained by exchanging left and right. The resulting bijection also
preserves the admissible F₂ marking. Boolean-operation preservation
and the global marked automorphism will be checked separately.

No ultrahomogeneity or model-theoretic language is assumed.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Swap the two marked embeddings of a finite bridge. -/
def PrebananaFiniteBridge.swap
    {M : PrebananaCountableBooleanModel}
    (p : PrebananaFiniteBridge M) : PrebananaFiniteBridge M where
  base := p.base
  left := p.right
  right := p.left

/-- Swapping both maps preserves the extension preorder. -/
theorem PrebananaFiniteBridge.swap_monotone
    {M : PrebananaCountableBooleanModel}
    {chain : ℕ → PrebananaFiniteBridge M}
    (hmono : Monotone chain) :
    Monotone (fun n => (chain n).swap) := by
  intro n m hnm
  obtain ⟨f, hleft, hright⟩ := hmono hnm
  exact ⟨f, hright, hleft⟩

/-- Coherence: two finite representatives of the same element on
the left necessarily agree on the right. Both representatives are
compared in a common later bridge. -/
theorem PrebananaFiniteBridge.right_eq_of_left_eq
    {M : PrebananaCountableBooleanModel}
    (chain : ℕ → PrebananaFiniteBridge M)
    (hmono : Monotone chain)
    (n m : ℕ)
    (a : (chain n).base.carrier)
    (b : (chain m).base.carrier)
    (hab : (chain n).left.hom a = (chain m).left.hom b) :
    (chain n).right.hom a = (chain m).right.hom b := by
  let N := max n m
  obtain ⟨f, hfL, hfR⟩ :
      chain n ≤ chain N := hmono (le_max_left n m)
  obtain ⟨g, hgL, hgR⟩ :
      chain m ≤ chain N := hmono (le_max_right n m)
  have hsame :
      f.hom a = g.hom b := by
    apply (chain N).left.injective
    exact (hfL a).trans (hab.trans (hgL b).symm)
  calc
    (chain n).right.hom a =
        (chain N).right.hom (f.hom a) := (hfR a).symm
    _ = (chain N).right.hom (g.hom b) :=
      congrArg (chain N).right.hom hsame
    _ = (chain m).right.hom b := hgR b

/-- Choose one finite left-hand representative of each element. -/
noncomputable def PrebananaFiniteBridge.chooseLeft
    {M : PrebananaCountableBooleanModel}
    (chain : ℕ → PrebananaFiniteBridge M)
    (hleft : ∀ x : M.carrier, ∃ n : ℕ,
      ∃ a : (chain n).base.carrier, (chain n).left.hom a = x)
    (x : M.carrier) : Σ n : ℕ, (chain n).base.carrier :=
  ⟨Classical.choose (hleft x),
    Classical.choose (Classical.choose_spec (hleft x))⟩

theorem PrebananaFiniteBridge.chooseLeft_spec
    {M : PrebananaCountableBooleanModel}
    (chain : ℕ → PrebananaFiniteBridge M)
    (hleft : ∀ x : M.carrier, ∃ n : ℕ,
      ∃ a : (chain n).base.carrier, (chain n).left.hom a = x)
    (x : M.carrier) :
    (chain (PrebananaFiniteBridge.chooseLeft chain hleft x).1).left.hom
      (PrebananaFiniteBridge.chooseLeft chain hleft x).2 = x := by
  exact Classical.choose_spec (Classical.choose_spec (hleft x))

/-- Coherent map determined by all finite bridge images. -/
noncomputable def PrebananaFiniteBridge.forward
    {M : PrebananaCountableBooleanModel}
    (chain : ℕ → PrebananaFiniteBridge M)
    (hleft : ∀ x : M.carrier, ∃ n : ℕ,
      ∃ a : (chain n).base.carrier, (chain n).left.hom a = x)
    (x : M.carrier) : M.carrier :=
  let c := PrebananaFiniteBridge.chooseLeft chain hleft x
  (chain c.1).right.hom c.2

/-- The coherent map agrees with the right-hand embedding on
every represented finite-stage element, not only on the chosen
representative. -/
theorem PrebananaFiniteBridge.forward_of_left
    {M : PrebananaCountableBooleanModel}
    (chain : ℕ → PrebananaFiniteBridge M)
    (hmono : Monotone chain)
    (hleft : ∀ x : M.carrier, ∃ n : ℕ,
      ∃ a : (chain n).base.carrier, (chain n).left.hom a = x)
    (n : ℕ) (a : (chain n).base.carrier) :
    PrebananaFiniteBridge.forward chain hleft
      ((chain n).left.hom a) = (chain n).right.hom a := by
  let c := PrebananaFiniteBridge.chooseLeft chain hleft
    ((chain n).left.hom a)
  have hspec :
      (chain c.1).left.hom c.2 = (chain n).left.hom a :=
    PrebananaFiniteBridge.chooseLeft_spec chain hleft _
  exact PrebananaFiniteBridge.right_eq_of_left_eq
    chain hmono c.1 n c.2 a hspec

/-- Two-sided exhaustion provides an actual global bijection:
the inverse is the same construction with left and right exchanged. -/
noncomputable def PrebananaFiniteBridge.limitEquiv
    {M : PrebananaCountableBooleanModel}
    (chain : ℕ → PrebananaFiniteBridge M)
    (hmono : Monotone chain)
    (hleft : ∀ x : M.carrier, ∃ n : ℕ,
      ∃ a : (chain n).base.carrier, (chain n).left.hom a = x)
    (hright : ∀ x : M.carrier, ∃ n : ℕ,
      ∃ a : (chain n).base.carrier, (chain n).right.hom a = x) :
    M.carrier ≃ M.carrier where
  toFun := PrebananaFiniteBridge.forward chain hleft
  invFun := PrebananaFiniteBridge.forward
    (fun n => (chain n).swap) hright
  left_inv := by
    intro x
    let c := PrebananaFiniteBridge.chooseLeft chain hleft x
    have hrepresent :
        (chain c.1).left.hom c.2 = x :=
      PrebananaFiniteBridge.chooseLeft_spec chain hleft x
    have hforward :
        PrebananaFiniteBridge.forward chain hleft x =
        (chain c.1).right.hom c.2 := rfl
    have hback := PrebananaFiniteBridge.forward_of_left
      (fun n => (chain n).swap)
      (PrebananaFiniteBridge.swap_monotone hmono)
      hright c.1 c.2
    change PrebananaFiniteBridge.forward
      (fun n => (chain n).swap) hright
      ((chain c.1).right.hom c.2) =
        (chain c.1).left.hom c.2 at hback
    calc
      PrebananaFiniteBridge.forward
          (fun n => (chain n).swap) hright
          (PrebananaFiniteBridge.forward chain hleft x) =
        PrebananaFiniteBridge.forward
          (fun n => (chain n).swap) hright
          ((chain c.1).right.hom c.2) :=
            congrArg _ hforward
      _ = (chain c.1).left.hom c.2 := hback
      _ = x := hrepresent
  right_inv := by
    intro x
    let chain' : ℕ → PrebananaFiniteBridge M :=
      fun n => (chain n).swap
    let c := PrebananaFiniteBridge.chooseLeft chain' hright x
    have hrepresent :
        (chain c.1).right.hom c.2 = x :=
      PrebananaFiniteBridge.chooseLeft_spec chain' hright x
    have hback :
        PrebananaFiniteBridge.forward chain' hright x =
        (chain c.1).left.hom c.2 := rfl
    have hforward := PrebananaFiniteBridge.forward_of_left
      chain hmono hleft c.1 c.2
    calc
      PrebananaFiniteBridge.forward chain hleft
          (PrebananaFiniteBridge.forward chain' hright x) =
        PrebananaFiniteBridge.forward chain hleft
          ((chain c.1).left.hom c.2) :=
          congrArg _ hback
      _ = (chain c.1).right.hom c.2 := hforward
      _ = x := hrepresent

/-- The global bijection preserves the F₂ marking, because each
finite bridge preserves that marking on both sides. -/
theorem PrebananaFiniteBridge.limitEquiv_preserves_mark
    {M : PrebananaCountableBooleanModel}
    (chain : ℕ → PrebananaFiniteBridge M)
    (hmono : Monotone chain)
    (hleft : ∀ x : M.carrier, ∃ n : ℕ,
      ∃ a : (chain n).base.carrier, (chain n).left.hom a = x)
    (hright : ∀ x : M.carrier, ∃ n : ℕ,
      ∃ a : (chain n).base.carrier, (chain n).right.hom a = x)
    (x : M.carrier) :
    M.μ (PrebananaFiniteBridge.limitEquiv chain hmono hleft hright x) =
      M.μ x := by
  let c := PrebananaFiniteBridge.chooseLeft chain hleft x
  have hrep :
      (chain c.1).left.hom c.2 = x :=
    PrebananaFiniteBridge.chooseLeft_spec chain hleft x
  calc
    M.μ (PrebananaFiniteBridge.limitEquiv chain hmono hleft hright x) =
      M.μ ((chain c.1).right.hom c.2) := rfl
    _ = (chain c.1).base.μ c.2 := (chain c.1).right.preserves_μ c.2
    _ = M.μ ((chain c.1).left.hom c.2) :=
      ((chain c.1).left.preserves_μ c.2).symm
    _ = M.μ x := congrArg M.μ hrep

end SuccessorTree.NonPrecompact
