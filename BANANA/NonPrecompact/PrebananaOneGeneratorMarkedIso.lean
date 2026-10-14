import BANANA.NonPrecompact.PrebananaUnaryKernelTransfer
import BANANA.NonPrecompact.PrebananaOneGeneratorFourValues
import BANANA.NonPrecompact.PrebananaAbstractGeneratedMarkedIso
import BANANA.NonPrecompact.PrebananaAmenabilityMeasureObstruction

/-!
# Canonical marked isomorphisms of one-generated Boolean subalgebras

If x and y are proper nonzero elements of (possibly different and
infinite) Boolean algebras, every Boolean-term equality at x
holds precisely when the corresponding equality holds at y.
The term-value map t(x) ↦ t(y) is therefore a genuine equivalence
of the generated Boolean subalgebras.

If in addition both elements have zero additive F₂ marking and
the marking vanishes at bottom and top, the equivalence preserves
marking. It maps each Boolean term to the same term at the target,
and so preserves all Boolean operations and the named generator.

The last lemma derives transitivity on proper nonzero zero-marked
elements from the exact tuple-generated ultrahomogeneity principle.
It does not assert construction of the countable Fraïssé limit;
ultrahomogeneity of that limit remains an external interface.
-/

namespace SuccessorTree.NonPrecompact

/-- Values of Boolean terms in two proper nonzero generators
correspond canonically, without requiring finite ambient carriers. -/
noncomputable def prebananaOneGeneratorTermRangeEquiv
    {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]
    (x : α) (y : β)
    (hbotX : x ≠ ⊥) (htopX : x ≠ ⊤)
    (hbotY : y ≠ ⊥) (htopY : y ≠ ⊤) :
    prebananaAbstractTermRange α (fun _ : Fin 1 => x) ≃
      prebananaAbstractTermRange β (fun _ : Fin 1 => y) := by
  classical
  let hEq : ∀ t u : PrebananaBooleanTerm 1,
      (t.evalBoolean (fun _ : Fin 1 => x) =
        u.evalBoolean (fun _ : Fin 1 => x)) ↔
      (t.evalBoolean (fun _ : Fin 1 => y) =
        u.evalBoolean (fun _ : Fin 1 => y)) :=
    prebananaOneGenerator_termEqualities_transfer x y
      hbotX htopX hbotY htopY
  let toY (z : prebananaAbstractTermRange α (fun _ : Fin 1 => x)) :
      prebananaAbstractTermRange β (fun _ : Fin 1 => y) :=
    ⟨(Classical.choose z.property).evalBoolean (fun _ : Fin 1 => y),
      ⟨Classical.choose z.property, rfl⟩⟩
  let toX (z : prebananaAbstractTermRange β (fun _ : Fin 1 => y)) :
      prebananaAbstractTermRange α (fun _ : Fin 1 => x) :=
    ⟨(Classical.choose z.property).evalBoolean (fun _ : Fin 1 => x),
      ⟨Classical.choose z.property, rfl⟩⟩
  refine {
    toFun := toY
    invFun := toX
    left_inv := ?_
    right_inv := ?_
  }
  · intro z
    apply Subtype.ext
    change (Classical.choose (toY z).property).evalBoolean
      (fun _ : Fin 1 => x) = z.val
    have hy :
        (Classical.choose (toY z).property).evalBoolean
          (fun _ : Fin 1 => y) =
        (Classical.choose z.property).evalBoolean
          (fun _ : Fin 1 => y) :=
      Classical.choose_spec (toY z).property
    exact ((hEq _ _).mpr hy).trans (Classical.choose_spec z.property)
  · intro z
    apply Subtype.ext
    change (Classical.choose (toX z).property).evalBoolean
      (fun _ : Fin 1 => y) = z.val
    have hx :
        (Classical.choose (toX z).property).evalBoolean
          (fun _ : Fin 1 => x) =
        (Classical.choose z.property).evalBoolean
          (fun _ : Fin 1 => x) :=
      Classical.choose_spec (toX z).property
    exact ((hEq _ _).mp hx).trans (Classical.choose_spec z.property)

/-- The canonical equivalence maps every Boolean term in x to
the same term evaluated at y. -/
theorem prebananaOneGeneratorTermRangeEquiv_eval
    {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]
    (x : α) (y : β)
    (hbotX : x ≠ ⊥) (htopX : x ≠ ⊤)
    (hbotY : y ≠ ⊥) (htopY : y ≠ ⊤)
    (t : PrebananaBooleanTerm 1) :
    (prebananaOneGeneratorTermRangeEquiv
      x y hbotX htopX hbotY htopY
      ⟨t.evalBoolean (fun _ : Fin 1 => x), ⟨t, rfl⟩⟩).val =
        t.evalBoolean (fun _ : Fin 1 => y) := by
  classical
  let z : prebananaAbstractTermRange α (fun _ : Fin 1 => x) :=
    ⟨t.evalBoolean (fun _ : Fin 1 => x), ⟨t, rfl⟩⟩
  have hz :
      (Classical.choose z.property).evalBoolean
        (fun _ : Fin 1 => x) =
      t.evalBoolean (fun _ : Fin 1 => x) :=
    Classical.choose_spec z.property
  change (Classical.choose z.property).evalBoolean
    (fun _ : Fin 1 => y) =
      t.evalBoolean (fun _ : Fin 1 => y)
  exact (prebananaOneGenerator_termEqualities_transfer
    x y hbotX htopX hbotY htopY _ t).mp hz

/-- The canonical equivalence preserves F₂ marking when both
generators are proper, nonzero, zero-marked elements. -/
theorem prebananaOneGeneratorTermRangeEquiv_preserves_mark
    {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]
    (μA : α → F2) (μB : β → F2)
    (hzeroA : μA ⊥ = 0) (htopA : μA ⊤ = 0)
    (haddA : ∀ z w : α, z ⊓ w = ⊥ →
      μA (z ⊔ w) = μA z + μA w)
    (hzeroB : μB ⊥ = 0) (htopB : μB ⊤ = 0)
    (haddB : ∀ z w : β, z ⊓ w = ⊥ →
      μB (z ⊔ w) = μB z + μB w)
    (x : α) (y : β)
    (hx : prebananaProperZeroMark μA x)
    (hy : prebananaProperZeroMark μB y)
    (z : prebananaAbstractTermRange α (fun _ : Fin 1 => x)) :
    μB ((prebananaOneGeneratorTermRangeEquiv
        x y hx.1 hx.2.1 hy.1 hy.2.1 z).val) =
      μA z.val := by
  classical
  let t := Classical.choose z.property
  let zX : prebananaGeneratedBooleanSubalgebra α
      (fun _ : Fin 1 => x) :=
    ⟨z.val, (prebananaGeneratedBooleanSubalgebra_mem_iff
      α (fun _ : Fin 1 => x) z.val).mpr z.property⟩
  let zY : prebananaGeneratedBooleanSubalgebra β
      (fun _ : Fin 1 => y) :=
    ⟨t.evalBoolean (fun _ : Fin 1 => y),
      (prebananaGeneratedBooleanSubalgebra_mem_iff
        β (fun _ : Fin 1 => y)
        (t.evalBoolean (fun _ : Fin 1 => y))).mpr ⟨t, rfl⟩⟩
  have hX : μA z.val = 0 :=
    prebananaOneGenerator_all_zero_mark
      μA hzeroA htopA haddA x hx.2.2 zX
  have hY :
      μB (t.evalBoolean (fun _ : Fin 1 => y)) = 0 :=
    prebananaOneGenerator_all_zero_mark
      μB hzeroB htopB haddB y hy.2.2 zY
  change μB (t.evalBoolean (fun _ : Fin 1 => y)) = μA z.val
  exact hY.trans hX.symm

/-- The zero-marked generators determine a genuine marked
isomorphism between their tuple-generated Boolean algebras. -/
noncomputable def prebananaOneGeneratorMarkedIso
    {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]
    (μA : α → F2) (μB : β → F2)
    (hzeroA : μA ⊥ = 0) (htopA : μA ⊤ = 0)
    (haddA : ∀ z w : α, z ⊓ w = ⊥ →
      μA (z ⊔ w) = μA z + μA w)
    (hzeroB : μB ⊥ = 0) (htopB : μB ⊤ = 0)
    (haddB : ∀ z w : β, z ⊓ w = ⊥ →
      μB (z ⊔ w) = μB z + μB w)
    (x : α) (y : β)
    (hx : prebananaProperZeroMark μA x)
    (hy : prebananaProperZeroMark μB y) :
    PrebananaAbstractGeneratedMarkedIso α β
      (fun _ : Fin 1 => x) (fun _ : Fin 1 => y) μA μB where
  equiv := prebananaOneGeneratorTermRangeEquiv
    x y hx.1 hx.2.1 hy.1 hy.2.1
  map_term := prebananaOneGeneratorTermRangeEquiv_eval
    x y hx.1 hx.2.1 hy.1 hy.2.1
  map_mark := prebananaOneGeneratorTermRangeEquiv_preserves_mark
    μA μB hzeroA htopA haddA hzeroB htopB haddB x y hx hy

/-- Any group action satisfying extension of finite marked
tuple-generated isomorphisms acts transitively on the proper
nonzero zero-marked Boolean elements. This is the exact
ultrahomogeneity consequence used in the circulation
non-amenability argument. -/
theorem prebananaProperZeroMark_orbit_of_ultrahomogeneity
    {α G : Type*} [BooleanAlgebra α] [Group G] [MulAction G α]
    (μ : α → F2)
    (hzero : μ ⊥ = 0) (htop : μ ⊤ = 0)
    (hadd : ∀ z w : α, z ⊓ w = ⊥ →
      μ (z ⊔ w) = μ z + μ w)
    (hhomogeneous :
      ∀ (n : ℕ) (xs ys : Fin n → α),
        PrebananaAbstractGeneratedMarkedIso α α xs ys μ μ →
        ∃ g : G, ∀ i : Fin n, g • xs i = ys i)
    (x y : α)
    (hx : prebananaProperZeroMark μ x)
    (hy : prebananaProperZeroMark μ y) :
    ∃ g : G, g • x = y := by
  obtain ⟨g, hg⟩ := hhomogeneous 1
    (fun _ : Fin 1 => x) (fun _ : Fin 1 => y)
    (prebananaOneGeneratorMarkedIso
      μ μ hzero htop hadd hzero htop hadd x y hx hy)
  exact ⟨g, hg 0⟩

end SuccessorTree.NonPrecompact
