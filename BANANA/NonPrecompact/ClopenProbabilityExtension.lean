import Mathlib.MeasureTheory.Measure.Content
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.Separation.Profinite

/-!
# Extending a clopen probability charge

On a compact Hausdorff totally disconnected space, a finitely additive
probability charge on clopens extends uniquely to a regular Borel
probability. The content of a compact set is the infimum of the charge of
its clopen covers. Disjoint compact sets can be separated by a clopen.
-/

namespace SuccessorTree.NonPrecompact

open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

variable {X : Type*} [TopologicalSpace X]

private def ClopenCovers (K : Compacts X) :=
  {U : Clopens X // (K : Set X) ⊆ (U : Set X)}

private noncomputable def compactMass (q : Clopens X → ℝ≥0) (K : Compacts X) : ℝ≥0∞ :=
  ⨅ U : ClopenCovers K, (q U.val : ℝ≥0∞)

private theorem compactMass_le (q : Clopens X → ℝ≥0) {K : Compacts X} {U : Clopens X}
    (h : (K : Set X) ⊆ (U : Set X)) : compactMass q K ≤ q U :=
  iInf_le _ (⟨U, h⟩ : ClopenCovers K)

private theorem compactMass_ne_top (q : Clopens X → ℝ≥0) (K : Compacts X) :
    compactMass q K ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top
    (compactMass_le q (U := ⊤) (by simp))

private theorem compactMass_mono (q : Clopens X → ℝ≥0) {K L : Compacts X}
    (hKL : (K : Set X) ⊆ L) : compactMass q K ≤ compactMass q L :=
  le_iInf fun U : ClopenCovers L => compactMass_le q (hKL.trans U.property)

private theorem charge_mono (q : Clopens X → ℝ≥0)
    (hadd : ∀ U V, Disjoint U V → q (U ⊔ V) = q U + q V) :
    Monotone q := by
  intro U V hUV
  have h := hadd U (V \ U) disjoint_sdiff_self_right
  rw [sup_sdiff_cancel_right hUV] at h
  rw [h]
  exact le_add_of_nonneg_right zero_le

private theorem compactMass_sup_le (q : Clopens X → ℝ≥0)
    (hadd : ∀ U V, Disjoint U V → q (U ⊔ V) = q U + q V) (K L : Compacts X) :
    compactMass q (K ⊔ L) ≤ compactMass q K + compactMass q L := by
  unfold compactMass
  rw [ENNReal.iInf_add]
  refine le_iInf fun U : ClopenCovers K => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun V : ClopenCovers L => ?_
  have hcover : ((K ⊔ L : Compacts X) : Set X) ⊆
      ((U.val ⊔ V.val : Clopens X) : Set X) :=
    union_subset_union U.property V.property
  refine (compactMass_le q hcover).trans ?_
  have h := hadd U.val (V.val \ U.val) disjoint_sdiff_self_right
  rw [sup_sdiff_self_right] at h
  rw [h, ENNReal.coe_add]
  exact add_le_add (le_refl _) (ENNReal.coe_le_coe.mpr (charge_mono q hadd sdiff_le))

variable [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]

private theorem compactMass_sup_of_disjoint (q : Clopens X → ℝ≥0)
    (hadd : ∀ U V, Disjoint U V → q (U ⊔ V) = q U + q V) {K L : Compacts X}
    (hd : Disjoint (K : Set X) L) :
    compactMass q (K ⊔ L) = compactMass q K + compactMass q L := by
  apply (compactMass_sup_le q hadd K L).antisymm
  have hsep : (K : Set X) ⊆ (L : Set X)ᶜ := by
    intro x hx hxL
    exact Set.disjoint_left.mp hd hx hxL
  obtain ⟨W, hW, hKW, hWL⟩ := exists_clopen_of_closed_subset_open K.isCompact.isClosed
    L.isCompact.isClosed.isOpen_compl hsep
  let C : Clopens X := ⟨W, hW⟩
  apply le_iInf
  intro U
  have hKU : (K : Set X) ⊆ (U.val ⊓ C : Clopens X) :=
    fun x hx => ⟨U.property (Or.inl hx), hKW hx⟩
  have hLU : (L : Set X) ⊆ (U.val \ C : Clopens X) :=
    fun x hx => ⟨U.property (Or.inr hx), fun hxW => hWL hxW hx⟩
  have hsplit := hadd (U.val ⊓ C) (U.val \ C) disjoint_inf_sdiff
  rw [sup_inf_sdiff] at hsplit
  change compactMass q K + compactMass q L ≤ (q U.val : ℝ≥0∞)
  rw [hsplit, ENNReal.coe_add]
  exact add_le_add (compactMass_le q hKU) (compactMass_le q hLU)

private noncomputable def clopenChargeContent (q : Clopens X → ℝ≥0)
    (hadd : ∀ U V, Disjoint U V → q (U ⊔ V) = q U + q V) : Content X where
  toFun K := (compactMass q K).toNNReal
  mono' K L h := ENNReal.toNNReal_mono (compactMass_ne_top q L) (compactMass_mono q h)
  sup_disjoint' K L hd _ _ := by
    rw [compactMass_sup_of_disjoint q hadd hd,
      ENNReal.toNNReal_add (compactMass_ne_top q K) (compactMass_ne_top q L)]
  sup_le' K L := by
    rw [← ENNReal.toNNReal_add (compactMass_ne_top q K) (compactMass_ne_top q L)]
    exact ENNReal.toNNReal_mono
      (ENNReal.add_ne_top.mpr ⟨compactMass_ne_top q K, compactMass_ne_top q L⟩)
      (compactMass_sup_le q hadd K L)

variable [MeasurableSpace X] [BorelSpace X]

private theorem clopenChargeContent_measure_clopen (q : Clopens X → ℝ≥0)
    (hadd : ∀ U V, Disjoint U V → q (U ⊔ V) = q U + q V) (U : Clopens X) :
    (clopenChargeContent q hadd).measure (U : Set X) = (q U : ℝ≥0∞) := by
  rw [Content.measure_apply _ U.isOpen.measurableSet, Content.outerMeasure_of_isOpen _ _ U.isOpen,
    Content.innerContent_of_isCompact _ U.isClosed.isCompact U.isOpen]
  let K : Compacts X := ⟨U, U.isClosed.isCompact⟩
  change ((compactMass q K).toNNReal : ℝ≥0∞) = (q U : ℝ≥0∞)
  rw [ENNReal.coe_toNNReal (compactMass_ne_top q K)]
  apply (compactMass_le q (K := K) (U := U) Subset.rfl).antisymm
  exact le_iInf fun V : ClopenCovers K =>
    ENNReal.coe_le_coe.mpr (charge_mono q hadd V.property)

omit [BorelSpace X] in
private theorem measure_le_open_of_clopen_le {μ ν : Measure X} [μ.Regular]
    (h : ∀ U : Clopens X, μ (U : Set X) ≤ ν (U : Set X)) {V : Set X}
    (hV : IsOpen V) : μ V ≤ ν V := by
  apply le_of_forall_lt
  intro r hr
  obtain ⟨K, hKV, hK, hrK⟩ := Measure.Regular.innerRegular hV r hr
  obtain ⟨U, hU, hKU, hUV⟩ := exists_clopen_of_closed_subset_open hK.isClosed hV hKV
  exact hrK.trans_le ((measure_mono hKU).trans ((h ⟨U, hU⟩).trans (measure_mono hUV)))

/-- A finitely additive probability charge on the clopens of a compact
Hausdorff totally disconnected space extends uniquely to a regular
Borel probability measure. -/
theorem existsUnique_regularProbability_of_clopenCharge (q : Clopens X → ℝ≥0)
    (hn : q ⊤ = 1) (hadd : ∀ U V, Disjoint U V → q (U ⊔ V) = q U + q V) :
    ∃! ν : Measure X, ν.Regular ∧ IsProbabilityMeasure ν ∧
      ∀ U : Clopens X, ν (U : Set X) = (q U : ℝ≥0∞) := by
  let μ := (clopenChargeContent q hadd).measure
  have hμ (U : Clopens X) : μ (U : Set X) = (q U : ℝ≥0∞) :=
    clopenChargeContent_measure_clopen q hadd U
  have hprob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    simpa only [Clopens.coe_top, hn, ENNReal.coe_one] using hμ ⊤
  let : μ.Regular := inferInstanceAs ((clopenChargeContent q hadd).measure.Regular)
  refine ⟨μ, ⟨inferInstance, hprob, hμ⟩, ?_⟩
  rintro ν ⟨hreg, _, hν⟩
  let : ν.Regular := hreg
  apply Measure.OuterRegular.ext_isOpen
  intro U hU
  exact (measure_le_open_of_clopen_le (fun W => ((hν W).trans (hμ W).symm).le) hU).antisymm
    (measure_le_open_of_clopen_le (fun W => ((hμ W).trans (hν W).symm).le) hU)

end SuccessorTree.NonPrecompact
