import BANANA.NonPrecompact.FirstOrderOligomorphicCategoricity

/-!
# Definable tuple Ramsey property and elementary equivalence

A finite family of formulas colours tuples by its truth values at a
parameter tuple. With finite covers by complete tuple types, existence
of a monochromatic target is expressed by an ordinary first-order
sentence. It therefore transfers to every elementarily equivalent model.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

universe u v w w'

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- Restricting matching tuples to the same coordinates preserves matching
formula types, including when coordinates are repeated. -/
theorem SameFormulaType.comp_indices {n m : ℕ} {a : Fin n → M} {b : Fin n → N}
    (h : SameFormulaType (L := L) a b) (i : Fin m → Fin n) :
    SameFormulaType (L := L) (a ∘ i) (b ∘ i) := by
  intro φ
  simpa only [Language.Formula.realize_relabel] using h (φ.relabel i)

/-- The finite-tuple form of the definable elementary embedding Ramsey
property. The bits of the colour are the truth values of a finite family
of formulas, evaluated with one shared finite tuple of parameters. -/
def HasDefinableTupleRamsey (L : Language.{u, v}) (M : Type w) [L.Structure M] : Prop :=
  ∀ {l r k c : ℕ} (a : Fin l → M) (b : Fin r → M) (p : Fin k → M)
    (φ : Fin c → L.Formula (Fin l ⊕ Fin k)),
    ∃ b' : Fin r → M, SameFormulaType (L := L) b b' ∧
      ∀ (i j : Fin l → Fin r),
        SameFormulaType (L := L) a (b ∘ i) → SameFormulaType (L := L) a (b ∘ j) →
        ∀ t, (φ t).Realize (Sum.elim (b' ∘ i) p) ↔ (φ t).Realize (Sum.elim (b' ∘ j) p)

private def onTargetIndices {l r k : ℕ} (φ : L.Formula (Fin l ⊕ Fin k))
    (i : Fin l → Fin r) : L.Formula (Fin k ⊕ Fin r) :=
  φ.relabel (Sum.elim (Sum.inr ∘ i) Sum.inl)

private theorem realize_onTargetIndices {l r k : ℕ} (φ : L.Formula (Fin l ⊕ Fin k))
    (i : Fin l → Fin r) (p : Fin k → M) (d : Fin r → M) :
    (onTargetIndices φ i).Realize (Sum.elim p d) ↔ φ.Realize (Sum.elim (d ∘ i) p) := by
  rw [onTargetIndices, Language.Formula.realize_relabel]
  have heq : Sum.elim p d ∘ Sum.elim (Sum.inr ∘ i) Sum.inl = Sum.elim (d ∘ i) p :=
    funext fun z => by cases z <;> rfl
  rw [heq]

/-- Definable colourings of elementary copies have monochromatic targets
in all models of a complete theory if this holds in one model with
finitely many realised types at each finite arity. -/
theorem HasDefinableTupleRamsey.of_elementarilyEquivalent
    (hMN : M ≅[L] N) (hM : HasDefinableTupleRamsey L M)
    (cover : ∀ n : ℕ, ∃ R : Finset (Fin n → M),
      ∀ b : Fin n → M, ∃ a : R, SameFormulaType (L := L) a.val b) :
    HasDefinableTupleRamsey L N := by
  classical
  intro l r k c a b p φ
  obtain ⟨A, hA⟩ := cover l
  obtain ⟨B, hB⟩ := cover r
  obtain ⟨a₀, ha⟩ := finite_formula_type_cover_of_elementarilyEquivalent hMN
    (fun s : A => s.val) hA a
  obtain ⟨b₀, hb⟩ := finite_formula_type_cover_of_elementarilyEquivalent hMN
    (fun s : B => s.val) hB b
  obtain ⟨θ, hθ⟩ := exists_formula_isolates_in_finite_type_cover
    (fun s : B => s.val) hB b₀.val
  let I := {i : Fin l → Fin r // SameFormulaType (L := L) a₀.val (b₀.val ∘ i)}
  let constraint : L.Formula (Fin k ⊕ Fin r) :=
    θ.relabel Sum.inr ⊓ Language.Formula.iInf fun (q : I × I × Fin c) =>
      (onTargetIndices (φ q.2.2) q.1.val).iff (onTargetIndices (φ q.2.2) q.2.1.val)
  have himp (p' : Fin k → M) : (constraint.iExs (Fin r)).Realize p' := by
    obtain ⟨d, hd, hmono⟩ := hM a₀.val b₀.val p' φ
    apply Language.Formula.realize_iExs.mpr
    refine ⟨d, Language.Formula.realize_inf.mpr ⟨?_, ?_⟩⟩
    · simpa only [Language.Formula.realize_relabel, Sum.elim_comp_inr] using (hθ d).mpr hd
    · apply Language.Formula.realize_iInf.mpr
      rintro ⟨i, j, t⟩
      exact Language.Formula.realize_iff.mpr <| (realize_onTargetIndices (φ t) i p' d).trans
        ((hmono i j i.property j.property t).trans (realize_onTargetIndices (φ t) j p' d).symm)
  have htarget := forall_realize_of_elementarilyEquivalent hMN _ himp p
  obtain ⟨d, hd⟩ := Language.Formula.realize_iExs.mp htarget
  obtain ⟨hD, hmono⟩ := Language.Formula.realize_inf.mp hd
  have hD' : θ.Realize d := by
    simpa only [Language.Formula.realize_relabel, Sum.elim_comp_inr] using hD
  have hsame : SameFormulaType (L := L) b₀.val d :=
    (isolates_formula_type_of_elementarilyEquivalent hMN hθ d).mp hD'
  refine ⟨d, hb.symm.trans hsame, fun i j hi hj t => ?_⟩
  let i' : I := ⟨i, ha.trans (hi.trans (hb.comp_indices i).symm)⟩
  let j' : I := ⟨j, ha.trans (hj.trans (hb.comp_indices j).symm)⟩
  have hmono' := Language.Formula.realize_iff.mp
    (Language.Formula.realize_iInf.mp hmono (i', j', t))
  exact (realize_onTargetIndices (φ t) i' p d).symm.trans
    (hmono'.trans (realize_onTargetIndices (φ t) j' p d))

end SuccessorTree.NonPrecompact
