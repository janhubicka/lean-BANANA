import BANANA.NonPrecompact.PrebananaCountableOnePointExtension
import Mathlib.Order.Ideal

/-!
# Finite marked Boolean bridges and cofinal back-and-forth chains

A finite bridge consists of a finite marked Boolean algebra A with
two genuine marked embeddings of A into the same countable marked
Boolean model. An extension bridge enlarges A without changing
either map on its original elements.

When the countable model has finite Boolean ambient subalgebras and
the finite-extension property, the one-point forth construction
extends a bridge to include any specified point in the left image.
Exchanging the two maps also gives the back step.

Mathlib's generic `Order.sequenceOfCofinals` then produces a
monotone sequence of finite bridges whose left and right images
both cover the countable model. This is a reusable algebraic
back-and-forth *chain*. Assembling the chain into a global marked
Boolean automorphism is a separate theorem.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- A finite marked Boolean model embedded twice into a countable
marked Boolean model. This representation records the two embeddings
without choosing a presentation of their images as subalgebras. -/
structure PrebananaFiniteBridge (M : PrebananaCountableBooleanModel) where
  base : PrebananaFiniteBooleanModel
  left : PrebananaFiniteToCountableEmbedding base M
  right : PrebananaFiniteToCountableEmbedding base M

/-- One bridge extends another when one marked embedding of their
finite carriers makes both diagrams commute on all elements. -/
instance (M : PrebananaCountableBooleanModel) :
    LE (PrebananaFiniteBridge M) where
  le p q :=
    ∃ f : PrebananaFiniteBooleanEmbedding p.base q.base,
      (∀ a : p.base.carrier,
        q.left.hom (f.hom a) = p.left.hom a) ∧
      (∀ a : p.base.carrier,
        q.right.hom (f.hom a) = p.right.hom a)

/-- Bridge extension is reflexive and transitive. Two different
finite presentations may represent the same maps, so use a preorder,
not an artificial antisymmetry axiom. -/
instance (M : PrebananaCountableBooleanModel) :
    Preorder (PrebananaFiniteBridge M) where
  le_refl p := by
    exact ⟨PrebananaFiniteBooleanEmbedding.id p.base,
      (fun _ => rfl), (fun _ => rfl)⟩
  le_trans p q r hpq hqr := by
    obtain ⟨f, hleft, hright⟩ := hpq
    obtain ⟨g, hleft', hright'⟩ := hqr
    refine ⟨g.comp f, ?_, ?_⟩
    · intro a
      change r.left.hom (g.hom (f.hom a)) = p.left.hom a
      exact (hleft' (f.hom a)).trans (hleft a)
    · intro a
      change r.right.hom (g.hom (f.hom a)) = p.right.hom a
      exact (hright' (f.hom a)).trans (hright a)

/-- The generic finite marked one-point forth theorem makes the
left-hand image contain any specified new point while preserving
the two maps on the original finite base. -/
theorem PrebananaFiniteBridge.exists_forth
    {M : PrebananaCountableBooleanModel}
    (hfinite : M.HasFiniteAmbients)
    (hext : M.HasFiniteExtensionProperty)
    (p : PrebananaFiniteBridge M) (x : M.carrier) :
    ∃ q : PrebananaFiniteBridge M,
      p ≤ q ∧
      ∃ y : q.base.carrier, q.left.hom y = x := by
  obtain ⟨B, f, i, h, y, hy, hleft, hright⟩ :=
    M.onePointForth hfinite hext p.base p.left p.right x
  refine ⟨⟨B, i, h⟩, ?_, ⟨y, hy⟩⟩
  exact ⟨f, hleft, hright⟩

/-- Reversing the two embeddings gives the corresponding back step,
in which the right-hand image contains any prescribed point. -/
theorem PrebananaFiniteBridge.exists_back
    {M : PrebananaCountableBooleanModel}
    (hfinite : M.HasFiniteAmbients)
    (hext : M.HasFiniteExtensionProperty)
    (p : PrebananaFiniteBridge M) (x : M.carrier) :
    ∃ q : PrebananaFiniteBridge M,
      p ≤ q ∧
      ∃ y : q.base.carrier, q.right.hom y = x := by
  obtain ⟨B, f, i, h, y, hy, hright, hleft⟩ :=
    M.onePointForth hfinite hext p.base p.right p.left x
  refine ⟨⟨B, h, i⟩, ?_, ⟨y, hy⟩⟩
  exact ⟨f, hleft, hright⟩

/-- The bridges whose left image contains x form a cofinal
subset of the bridge preorder. -/
noncomputable def PrebananaFiniteBridge.leftCofinal
    {M : PrebananaCountableBooleanModel}
    (hfinite : M.HasFiniteAmbients)
    (hext : M.HasFiniteExtensionProperty)
    (x : M.carrier) : Order.Cofinal (PrebananaFiniteBridge M) where
  carrier := {p | ∃ y : p.base.carrier, p.left.hom y = x}
  isCofinal := by
    intro p
    obtain ⟨q, hpq, hx⟩ :=
      PrebananaFiniteBridge.exists_forth hfinite hext p x
    exact ⟨q, hx, hpq⟩

/-- Similarly the bridges whose right image contains x are cofinal. -/
noncomputable def PrebananaFiniteBridge.rightCofinal
    {M : PrebananaCountableBooleanModel}
    (hfinite : M.HasFiniteAmbients)
    (hext : M.HasFiniteExtensionProperty)
    (x : M.carrier) : Order.Cofinal (PrebananaFiniteBridge M) where
  carrier := {p | ∃ y : p.base.carrier, p.right.hom y = x}
  isCofinal := by
    intro p
    obtain ⟨q, hpq, hx⟩ :=
      PrebananaFiniteBridge.exists_back hfinite hext p x
    exact ⟨q, hx, hpq⟩

/-- The cofinal-chain form of marked Boolean back-and-forth.

Starting at any finite bridge, construct a monotonically enlarging
sequence that exhausts the model simultaneously in the ranges of
the left and right embeddings. This statement is independent of
any first-order model-theoretic language encoding. -/
theorem PrebananaFiniteBridge.exists_exhaustive_chain
    {M : PrebananaCountableBooleanModel}
    (hfinite : M.HasFiniteAmbients)
    (hext : M.HasFiniteExtensionProperty)
    (p : PrebananaFiniteBridge M) :
    ∃ chain : ℕ → PrebananaFiniteBridge M,
      Monotone chain ∧
      (∀ x : M.carrier, ∃ n : ℕ,
        ∃ a : (chain n).base.carrier, (chain n).left.hom a = x) ∧
      (∀ x : M.carrier, ∃ n : ℕ,
        ∃ a : (chain n).base.carrier, (chain n).right.hom a = x) := by
  classical
  letI : Encodable (Sum M.carrier M.carrier) :=
    Encodable.ofCountable _
  let D : Sum M.carrier M.carrier →
      Order.Cofinal (PrebananaFiniteBridge M) :=
    Sum.elim
      (PrebananaFiniteBridge.leftCofinal hfinite hext)
      (PrebananaFiniteBridge.rightCofinal hfinite hext)
  let chain : ℕ → PrebananaFiniteBridge M :=
    Order.sequenceOfCofinals p D
  refine ⟨chain, Order.sequenceOfCofinals.monotone p D, ?_, ?_⟩
  · intro x
    have h :=
      Order.sequenceOfCofinals.encode_mem p D (Sum.inl x)
    exact ⟨Encodable.encode (Sum.inl x : Sum M.carrier M.carrier) + 1, h⟩
  · intro x
    have h :=
      Order.sequenceOfCofinals.encode_mem p D (Sum.inr x)
    exact ⟨Encodable.encode (Sum.inr x : Sum M.carrier M.carrier) + 1, h⟩

end SuccessorTree.NonPrecompact
