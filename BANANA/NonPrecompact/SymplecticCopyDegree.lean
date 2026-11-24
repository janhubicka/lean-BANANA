import BANANA.NonPrecompact.SymplecticCopySystem
import BANANA.NonPrecompact.SymplecticPointColouring

/-!
# Copy Ramsey degrees of finite binary alternating spaces

The persistent colouring on lines applies to every embedded nondegenerate
target of twice the required dimension. The generic amalgamation argument
propagates the unbounded degree of a line to every nonzero source.
-/

namespace SuccessorTree.NonPrecompact.FiniteAlternatingSpace

open LinearMap Module
open scoped Matrix

/-- The one-dimensional alternating space over the binary field. -/
def line : FiniteAlternatingSpace where
  carrier := F2
  addCommGroup := inferInstance
  module := inferInstance
  finiteDimensional := inferInstance
  form := 0
  alternating := fun _ => rfl

private def lineEmbedding (A : FiniteAlternatingSpace) (x : A.carrier) (hx : x ≠ 0) :
    Embedding line A where
  linear := LinearMap.toSpanSingleton F2 A.carrier x
  injective := LinearMap.ker_eq_bot.mp (LinearMap.ker_toSpanSingleton F2 hx)
  preserves_form a b := by
    change F2 at a b
    change A.form (a • x) (b • x) = 0
    rw [BilinForm.smul_left, BilinForm.smul_right, A.alternating.self_eq_zero]
    simp

/-- Unlabelled copies of the one-dimensional source are exactly the
one-dimensional subspaces. -/
noncomputable def lineCopyEquiv (A : FiniteAlternatingSpace) :
    Copy line A ≃ {S : Submodule F2 A.carrier // finrank F2 S = 1} where
  toFun p := ⟨p.val, by
    obtain ⟨f, hf⟩ := p.property
    rw [← hf, LinearMap.finrank_range_of_inj f.injective]
    exact CommSemiring.finrank_self F2⟩
  invFun S := ⟨S.val, by
    obtain ⟨x, hx, hspan⟩ := (finrank_eq_one_iff' (K := F2) (V := ↥S.val)).mp S.property
    have hx' : x.val ≠ 0 := fun h => hx (Subtype.ext h)
    refine ⟨lineEmbedding A x.val hx', ?_⟩
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      exact S.val.smul_mem a x.property
    · intro y hy
      obtain ⟨a, ha⟩ := hspan ⟨y, hy⟩
      exact ⟨a, congrArg Subtype.val ha⟩⟩
  left_inv p := Subtype.ext rfl
  right_inv p := Subtype.ext rfl

private abbrev HyperbolicCoordinates (q : ℕ) := (Fin q → F2) × (Fin q → F2)

private def hyperbolicForm (q : ℕ) : LinearMap.BilinForm F2 (HyperbolicCoordinates q) :=
  LinearMap.mk₂ F2 (fun x y : HyperbolicCoordinates q => x.1 ⬝ᵥ y.2 - y.1 ⬝ᵥ x.2)
    (fun _ _ _ => by simp [add_dotProduct, dotProduct_add, sub_add_sub_comm])
    (fun _ _ _ => by simp [smul_dotProduct, dotProduct_smul, mul_sub])
    (fun _ _ _ => by simp [add_dotProduct, dotProduct_add, sub_add_sub_comm])
    (fun _ _ _ => by simp [smul_dotProduct, dotProduct_smul, mul_sub])

private theorem hyperbolicForm_isAlt (q : ℕ) : (hyperbolicForm q).IsAlt := by
  intro x
  change x.1 ⬝ᵥ x.2 - x.1 ⬝ᵥ x.2 = 0
  exact sub_self _

private theorem hyperbolicForm_nondegenerate (q : ℕ) : (hyperbolicForm q).Nondegenerate := by
  have hleft : (hyperbolicForm q).SeparatingLeft := by
    intro x hx
    apply Prod.ext <;> ext i
    · have h := hx (0, Pi.single i 1)
      change x.1 ⬝ᵥ Pi.single i 1 - (0 : Fin q → F2) ⬝ᵥ x.2 = 0 at h
      simpa [dotProduct_single_one] using h
    · have h := hx (Pi.single i 1, 0)
      change x.1 ⬝ᵥ (0 : Fin q → F2) - Pi.single i 1 ⬝ᵥ x.2 = 0 at h
      simpa [single_one_dotProduct] using h
  refine ⟨hleft, fun x hx => hleft x (fun y => ?_)⟩
  rw [← neg_eq_zero, (hyperbolicForm_isAlt q).neg_eq, hx]

/-- The nondegenerate target of dimension `2 * q`. -/
def hyperbolicTarget (q : ℕ) : FiniteAlternatingSpace where
  carrier := HyperbolicCoordinates q
  addCommGroup := inferInstance
  module := inferInstance
  finiteDimensional := inferInstance
  form := hyperbolicForm q
  alternating := hyperbolicForm_isAlt q

theorem hyperbolicTarget_finrank (q : ℕ) :
    finrank F2 (hyperbolicTarget q).carrier = 2 * q := by
  change finrank F2 (HyperbolicCoordinates q) = 2 * q
  rw [Module.finrank_prod]
  simp [two_mul]

theorem hyperbolicTarget_nondegenerate (q : ℕ) : (hyperbolicTarget q).form.Nondegenerate :=
  hyperbolicForm_nondegenerate q

private theorem range_nondegenerate {A C : FiniteAlternatingSpace}
    (f : Embedding A C) (h : A.form.Nondegenerate) :
    (C.form.restrict (LinearMap.range f.linear)).Nondegenerate := by
  let e := LinearEquiv.ofInjective f.linear f.injective
  have hform : BilinForm.congr e A.form = C.form.restrict (LinearMap.range f.linear) := by
    apply LinearMap.ext₂
    intro x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [BilinForm.congr_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact (f.preserves_form x y).symm
  rw [← hform]
  exact h.congr e

/-- The one-dimensional source has no finite copy Ramsey degree bound. -/
theorem line_copyRamseyDegree_infinite (t : ℕ) :
    ¬ copySystem.CopyRamseyDegreeLE line t := by
  classical
  intro h
  let q := 2 ^ (t + 1)
  have hq : 0 < q := by positivity
  let _ : NeZero q := ⟨hq.ne'⟩
  obtain ⟨C, hC⟩ := h (hyperbolicTarget q) q hq
  change FiniteAlternatingSpace at C
  obtain ⟨colour, hcolour⟩ :=
    exists_symplecticPointColouring C.form C.alternating (t + 1) (Nat.succ_pos t)
  let r : Fin q ≃+* ZMod q := ZMod.finEquiv q
  let c : copySystem.Copy line C → Fin q :=
    fun p => r.symm (colour (lineCopyEquiv C p))
  obtain ⟨f, hf⟩ := hC c
  change Embedding (hyperbolicTarget q) C at f
  let _ := copySystem.copyFintype line (hyperbolicTarget q)
  have hall : copySystem.coloursInside c f = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro k
    obtain ⟨S, hS, hcol⟩ := hcolour (LinearMap.range f.linear)
      (range_nondegenerate f (hyperbolicTarget_nondegenerate q))
      ((LinearMap.finrank_range_of_inj f.injective).trans (hyperbolicTarget_finrank q)) (r k)
    let p := (lineCopyEquiv C).symm S
    have hsub : copySystem.Subcopy p (copySystem.range f) := hS
    obtain ⟨P, hP⟩ := (copySystem.subcopy_range_iff f p).mp hsub
    refine Finset.mem_image.mpr ⟨P, Finset.mem_univ _, ?_⟩
    rw [hP]
    simp [c, p, hcol]
  rw [hall, Finset.card_univ, Fintype.card_fin] at hf
  have hlt : t < q := (Nat.lt_succ_self t).trans Nat.lt_two_pow_self
  exact hlt.not_ge hf

/-- A positive-dimensional source has infinite copy Ramsey degree. -/
theorem positive_copyRamseyDegree_infinite (A : FiniteAlternatingSpace)
    (hA : 0 < finrank F2 A.carrier) (t : ℕ) :
    ¬ copySystem.CopyRamseyDegreeLE A t := by
  classical
  intro h
  obtain ⟨x, hx⟩ := finrank_pos_iff_exists_ne_zero.mp hA
  exact line_copyRamseyDegree_infinite _
    (amalgamation.copyRamseyDegreeLE_of_embedding (lineEmbedding A x hx) h)

/-- Every target has exactly one copy of a zero-dimensional source. -/
@[instance_reducible]
private noncomputable def zero_copy_unique (A B : FiniteAlternatingSpace)
    (hA : finrank F2 A.carrier = 0) : Unique (copySystem.Copy A B) := by
  change Unique (Copy A B)
  letI : Subsingleton A.carrier := (Module.finrank_eq_zero_iff_of_free F2 A.carrier).mp hA
  let f : Embedding A B := ⟨0, fun _ _ _ => Subsingleton.elim _ _, fun x y => by
    rw [Subsingleton.elim x 0]
    simp⟩
  refine { default := Copy.ofEmbedding f, uniq := fun p => Subtype.ext ?_ }
  obtain ⟨g, hg⟩ := p.property
  rw [← hg]
  change LinearMap.range g.linear = LinearMap.range f.linear
  have hzero : g.linear = 0 := LinearMap.ext fun x => by rw [Subsingleton.elim x 0]; simp
  simp [f, hzero]

/-- Complete classification. A zero-dimensional source has degree one,
and there is no finite bound for any positive-dimensional source. -/
theorem copyRamseyDegree_classification (A : FiniteAlternatingSpace) (t : ℕ) :
    copySystem.CopyRamseyDegreeLE A t ↔ finrank F2 A.carrier = 0 ∧ 1 ≤ t := by
  classical
  constructor
  · intro h
    have hA : finrank F2 A.carrier = 0 := by
      by_contra hn
      exact positive_copyRamseyDegree_infinite A (Nat.pos_of_ne_zero hn) t h
    refine ⟨hA, ?_⟩
    obtain ⟨C, hC⟩ := h A 1 (by decide)
    let c : copySystem.Copy A C → Fin 1 := fun _ => 0
    obtain ⟨f, hf⟩ := hC c
    let _ := copySystem.copyFintype A A
    have hm : 0 ∈ copySystem.coloursInside c f :=
      Finset.mem_image.mpr ⟨copySystem.range (copySystem.idEmb A), Finset.mem_univ _, rfl⟩
    exact (Finset.card_pos.mpr ⟨0, hm⟩).trans_le hf
  · rintro ⟨hA, ht⟩ B r _
    refine ⟨B, fun c => ⟨copySystem.idEmb B, ?_⟩⟩
    let _ : Unique (copySystem.Copy A B) := zero_copy_unique A B hA
    let _ := copySystem.copyFintype A B
    refine le_trans (Finset.card_le_one.mpr ?_) ht
    intro a ha b hb
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp ha
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hb
    rw [← hp, ← hq, Subsingleton.elim p q]

end SuccessorTree.NonPrecompact.FiniteAlternatingSpace
