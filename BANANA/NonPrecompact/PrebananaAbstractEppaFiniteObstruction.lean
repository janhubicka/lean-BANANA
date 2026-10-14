import BANANA.NonPrecompact.PrebananaEppaObstruction

/-!
# Finite-order obstruction to extending the pre-BANANA partial isomorphism

The circulated proof uses the partial isomorphism taking one nonzero
Boolean element to its proper enlargement by a disjoint nonzero
element. The finite obstruction does not depend on the parity mark:
no order automorphism of **any finite partially ordered set** can
send an element to a strictly greater one.

Indeed, the set of elements below x is strictly smaller than the
set of elements below its proper enlargement, while an order
automorphism preserves the cardinality of the lower set.

This module records the abstract finite ambient obstruction and
specialises it to the indicated two elements of the unmarked
three-atom Boolean algebra. Constructing the isomorphism between
the two generated four-element subalgebras is a separate step.
-/

namespace SuccessorTree.NonPrecompact

/-- A finite-order automorphism cannot move an element strictly
upwards in the partial order. -/
theorem finiteOrderIso_no_strict_increase
    {α : Type*} [PartialOrder α] [Fintype α]
    (e : α ≃o α) (x : α) :
    ¬ x < e x := by
  classical
  intro hx
  let low : α → Finset α :=
    fun z => Finset.univ.filter (fun y => y ≤ z)
  have himage : (low x).image e = low (e x) := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      have hwle : w ≤ x := (Finset.mem_filter.mp hw).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, e.monotone hwle⟩
    · intro hz
      have hzle : z ≤ e x := (Finset.mem_filter.mp hz).2
      have hwle : e.symm z ≤ x := by
        simpa only [e.symm_apply_apply] using e.symm.monotone hzle
      exact Finset.mem_image.mpr
        ⟨e.symm z,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwle⟩,
          e.apply_symm_apply z⟩
  have hsubset : low x ⊆ low (e x) := by
    intro z hz
    have hzle : z ≤ x := (Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hzle.trans hx.le⟩
  have hyes : e x ∈ low (e x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
  have hnot : e x ∉ low x := by
    intro h
    exact (not_le_of_gt hx) ((Finset.mem_filter.mp h).2)
  have hstrict : low x ⊂ low (e x) :=
    (Finset.ssubset_iff_of_subset hsubset).2 ⟨e x, hyes, hnot⟩
  have hsmaller : (low x).card < (low (e x)).card :=
    Finset.card_lt_card hstrict
  have hequal : (low x).card = (low (e x)).card := by
    rw [← himage]
    exact (Finset.card_image_of_injective (low x) e.injective).symm
  omega

/-- A strictly order-preserving embedding into a finite structure
cannot have its image extended by an automorphism which moves
one embedded element to a proper enlargement. -/
theorem finiteOrderIso_no_strict_partial_extension
    {α β : Type*}
    [PartialOrder α] [PartialOrder β] [Fintype β]
    (f : α → β) (hf : StrictMono f)
    {x y : α} (hxy : x < y) :
    ¬ ∃ e : β ≃o β, e (f x) = f y := by
  rintro ⟨e, he⟩
  apply finiteOrderIso_no_strict_increase e (f x)
  simpa only [he] using hf hxy

/-- In the three-atom Boolean algebra, the element comprising
atom zero is strictly below the union of atoms zero and one. -/
theorem prebananaThreeAtoms_strict_inclusion :
    ({0} : Finset (Fin 3)) < {0, 1} := by
  decide

/-- The concrete pre-BANANA EPPA obstruction is already impossible
in every finite ordered ambient extension, independently of its
marking: an automorphism cannot extend the map from the first
element to its strict enlargement. -/
theorem prebananaThreeAtoms_no_finite_extension
    {β : Type*} [PartialOrder β] [Fintype β]
    (f : Finset (Fin 3) → β) (hf : StrictMono f) :
    ¬ ∃ e : β ≃o β,
      e (f ({0} : Finset (Fin 3))) = f ({0, 1} : Finset (Fin 3)) :=
  finiteOrderIso_no_strict_partial_extension
    f hf prebananaThreeAtoms_strict_inclusion

end SuccessorTree.NonPrecompact
