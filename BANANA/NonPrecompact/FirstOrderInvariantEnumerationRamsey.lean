import BANANA.NonPrecompact.FirstOrderInvariantTypes

/-!
# Definable tuple Ramsey from an invariant enumeration type

Realise the invariant type in a model of the elementary diagram. The
coordinates corresponding to the colouring parameters then satisfy the
colour agreement conditions on the original target. An existential
formula transfers these parameters back to the original model. When
finite tuple types are isolated, the transferred parameters have the
original parameter type and give a monochromatic copy of the target.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

universe u v w

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- Realising an invariant enumeration type gives a parameter tuple in an
elementary extension with the original parameter type. The colours at
those parameters agree on the relevant subtuples of the original target. -/
theorem exists_colour_agreement_in_elementary_extension
    (q : (L.elementaryDiagram M).CompleteType M) (hq : IsInvariantType q)
    (hExt : ∀ (φ : L.Formula M), φ.Realize (id : M → M) →
      Language.Formula.equivSentence ((L.lhomWithConstants M).onFormula φ) ∈ q)
    {l r k c : ℕ} (a : Fin l → M) (b : Fin r → M) (d : Fin k → M)
    (colour : Fin c → L.Formula (Fin l ⊕ Fin k)) :
    let I := {i : Fin l → Fin r // SameFormulaType (L := L) a (b ∘ i)}
    ∃ (N : Type (max u v w)) (_ : L.Structure N) (_ : Nonempty N)
        (e : M ↪ₑ[L] N) (dN : Fin k → N), SameFormulaType (L := L) d dN ∧
      ∀ (i j : I) (t : Fin c),
        (colour t).Realize (Sum.elim ((e ∘ b) ∘ i.val) dN) ↔
          (colour t).Realize (Sum.elim ((e ∘ b) ∘ j.val) dN) := by
  intro I
  obtain ⟨N, v, hv⟩ := Language.Theory.exists_modelType_is_realized_in (L.elementaryDiagram M) q
  let _ : L.Structure N := (L.lhomWithConstants M).reduct N
  let e := Language.ElementaryEmbedding.ofModelsElementaryDiagram L M N
  have hmem (ψ : L[[M]].Formula M) :
      Language.Formula.equivSentence ψ ∈ q ↔ ψ.Realize v := by
    rw [← hv]
    exact Language.Theory.CompleteType.formula_mem_typeOf
  have hExtN (ψ : L.Formula M) (hψ : ψ.Realize (id : M → M)) : ψ.Realize v :=
    (Language.LHom.realize_onFormula _ _).mp ((hmem _).mp (hExt ψ hψ))
  have hθN (θ : L.Formula (Fin k)) (hθ : θ.Realize d) : θ.Realize (v ∘ d) := by
    apply (Language.Formula.realize_relabel (φ := θ) (g := d) (v := v)).mp
    apply hExtN
    rw [Language.Formula.realize_relabel, Function.id_comp]
    exact hθ
  have htype : SameFormulaType (L := L) d (v ∘ d) := by
    intro θ
    refine ⟨hθN θ, fun h => ?_⟩
    by_contra hn
    exact (hθN θ.not hn) h
  let relabelParameters (t : Fin c) : L.Formula (Fin l ⊕ M) :=
    (colour t).relabel (Sum.elim Sum.inl (Sum.inr ∘ d))
  have hColour (i : I) (t : Fin c) :
      Language.Formula.equivSentence (formulaWithParameters (relabelParameters t) (b ∘ i.val)) ∈ q
        ↔ (colour t).Realize (Sum.elim ((e ∘ b) ∘ i.val) (v ∘ d)) := by
    simp only [hmem, realize_formulaWithParameters_of_expansion, relabelParameters, Language.Formula.realize_relabel]
    have h :
        Sum.elim (fun j => (L.con ((b ∘ i.val) j) : N)) v ∘
          Sum.elim Sum.inl (Sum.inr ∘ d) =
            Sum.elim ((e ∘ b) ∘ i.val) (v ∘ d) :=
      funext fun s => by cases s <;> rfl
    exact Iff.of_eq (congrArg (colour t).Realize h)
  have hmonoN (i j : I) (t : Fin c) :
      (colour t).Realize (Sum.elim ((e ∘ b) ∘ i.val) (v ∘ d)) ↔
        (colour t).Realize (Sum.elim ((e ∘ b) ∘ j.val) (v ∘ d)) :=
    (hColour i t).symm.trans <|
      (hq (relabelParameters t) (b ∘ i.val) (b ∘ j.val) (i.property.symm.trans j.property)).trans
        (hColour j t)
  exact ⟨N, inferInstance, inferInstance, e, v ∘ d, htype, hmonoN⟩

/-- An invariant extension of the type of the entire enumeration entails
definable tuple Ramsey in any model with isolated finite tuple types. -/
theorem HasDefinableTupleRamsey.of_invariantEnumerationType
    (hIsolate : ∀ r (b : Fin r → M), ∃ θ : L.Formula (Fin r),
      ∀ z : Fin r → M, θ.Realize z ↔ SameFormulaType (L := L) b z)
    (q : (L.elementaryDiagram M).CompleteType M) (hq : IsInvariantType q)
    (hExt : ∀ (φ : L.Formula M), φ.Realize (id : M → M) →
      Language.Formula.equivSentence ((L.lhomWithConstants M).onFormula φ) ∈ q) :
    HasDefinableTupleRamsey L M := by
  classical
  intro l r k c a b d colour
  obtain ⟨θb, hθb⟩ := hIsolate r b
  obtain ⟨θd, hθd⟩ := hIsolate k d
  obtain ⟨_, _, _, e, dN, htype, hmonoN⟩ :=
    exists_colour_agreement_in_elementary_extension q hq hExt a b d colour
  let I := {i : Fin l → Fin r // SameFormulaType (L := L) a (b ∘ i)}
  have hθN : θd.Realize dN := (htype θd).mp ((hθd d).mpr (SameFormulaType.refl d))
  let targetFirst (i : I) (t : Fin c) : L.Formula (Fin r ⊕ Fin k) :=
    (colour t).relabel (Sum.map i.val id)
  let paramsConstraint : L.Formula (Fin r ⊕ Fin k) :=
    θd.relabel Sum.inr ⊓ Language.Formula.iInf fun (q : I × I × Fin c) =>
      (targetFirst q.1 q.2.2).iff (targetFirst q.2.1 q.2.2)
  have hN : (paramsConstraint.iExs (Fin k)).Realize (e ∘ b) := by
    apply Language.Formula.realize_iExs.mpr
    refine ⟨dN, Language.Formula.realize_inf.mpr ⟨?_, ?_⟩⟩
    · simpa only [Language.Formula.realize_relabel, Sum.elim_comp_inr] using hθN
    · apply Language.Formula.realize_iInf.mpr
      rintro ⟨i, j, t⟩
      apply Language.Formula.realize_iff.mpr
      simpa only [targetFirst, Language.Formula.realize_relabel, Sum.elim_comp_map, Function.comp_id]
        using hmonoN i j t
  have hM := (e.map_formula _ b).mp hN
  obtain ⟨d', hd'⟩ := Language.Formula.realize_iExs.mp hM
  obtain ⟨hmatchd', hmonod'⟩ := Language.Formula.realize_inf.mp hd'
  have hmatchd : SameFormulaType (L := L) d d' :=
    (hθd d').mp (by simpa only [Language.Formula.realize_relabel, Sum.elim_comp_inr] using hmatchd')
  let targetConstraint : L.Formula (Fin k ⊕ Fin r) :=
    θb.relabel Sum.inr ⊓ Language.Formula.iInf fun (q : I × I × Fin c) =>
      (onTargetIndices (colour q.2.2) q.1.val).iff (onTargetIndices (colour q.2.2) q.2.1.val)
  have htargetd' : (targetConstraint.iExs (Fin r)).Realize d' := by
    apply Language.Formula.realize_iExs.mpr
    refine ⟨b, Language.Formula.realize_inf.mpr ⟨?_, ?_⟩⟩
    · simpa only [Language.Formula.realize_relabel, Sum.elim_comp_inr] using
        (hθb b).mpr (SameFormulaType.refl b)
    · apply Language.Formula.realize_iInf.mpr
      rintro ⟨i, j, t⟩
      have h := Language.Formula.realize_iff.mp
        (Language.Formula.realize_iInf.mp hmonod' (i, j, t))
      apply Language.Formula.realize_iff.mpr
      refine (realize_onTargetIndices (colour t) i.val d' b).trans
        (Iff.trans ?_ (realize_onTargetIndices (colour t) j.val d' b).symm)
      simpa only [targetFirst, Language.Formula.realize_relabel, Sum.elim_comp_map, Function.comp_id]
        using h
  have htarget := (hmatchd _).mpr htargetd'
  obtain ⟨b', hb'⟩ := Language.Formula.realize_iExs.mp htarget
  obtain ⟨hb', hmono⟩ := Language.Formula.realize_inf.mp hb'
  have hmatch : θb.Realize b' := by
    simpa only [Language.Formula.realize_relabel, Sum.elim_comp_inr] using hb'
  refine ⟨b', (hθb b').mp hmatch, fun i j hi hj t => ?_⟩
  have h := Language.Formula.realize_iff.mp
    (Language.Formula.realize_iInf.mp hmono (⟨i, hi⟩, ⟨j, hj⟩, t))
  exact (realize_onTargetIndices (colour t) i _ _).symm.trans <|
    h.trans (realize_onTargetIndices (colour t) j _ _)

/-- In a model with isolated finite tuple types, definable tuple Ramsey and
the existence of an invariant enumeration extension are equivalent. -/
theorem hasDefinableTupleRamsey_iff_exists_invariantEnumerationType [Nonempty M]
    (hIsolate : ∀ r (b : Fin r → M), ∃ θ : L.Formula (Fin r),
      ∀ z : Fin r → M, θ.Realize z ↔ SameFormulaType (L := L) b z) :
    HasDefinableTupleRamsey L M ↔
      ∃ q : (L.elementaryDiagram M).CompleteType M, IsInvariantType q ∧
        ∀ (φ : L.Formula M), φ.Realize (id : M → M) →
          Language.Formula.equivSentence ((L.lhomWithConstants M).onFormula φ) ∈ q := by
  constructor
  · intro h
    exact h.exists_invariantType hIsolate id
  · rintro ⟨q, hq, hExt⟩
    exact HasDefinableTupleRamsey.of_invariantEnumerationType hIsolate q hq hExt



end SuccessorTree.NonPrecompact
