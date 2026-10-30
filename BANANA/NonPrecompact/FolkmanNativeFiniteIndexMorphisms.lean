import BANANA.NonPrecompact.FolkmanNativeFiniteAtomIndex

/-!
# Native non-unital Folkman maps in finite-index coordinates

The original finite Boolean-ring isomorphisms from
FolkmanNativeFiniteAtomIndex conjugate any native non-unital ring map
to a map between finite atom powersets.  Addition, multiplication,
zero and injectivity are transported without assuming preservation
of the ring unit.  When both source and target pairings are additive,
pairing preservation on the native carriers implies preservation
of the corresponding finite indexed matrix pairings on all supports.

These are morphism-level companions to the finite-object representation.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff BigOperators

local instance folkmanAsBoolAlgFiniteForFinMaps
    (α : Type*) [Fintype α] : Fintype (AsBoolAlg α) :=
  Fintype.ofEquiv α toBoolAlg

/-- Inverse finite-index encoding takes the empty support to zero. -/
theorem folkmanNativeFiniteRingCode_symm_zero
    (α : Type*) [BooleanRing α] [Fintype α] :
    (folkmanNativeFiniteRingCodeEquiv α).symm ∅ = 0 := by
  classical
  let e := folkmanNativeFiniteRingCodeEquiv α
  apply e.injective
  change e (e.symm ∅) = e (0 : α)
  rw [e.apply_symm_apply, folkmanNativeFiniteRingCode_zero]

/-- Inverse coding respects symmetric difference. -/
theorem folkmanNativeFiniteRingCode_symm_add
    (α : Type*) [BooleanRing α] [Fintype α]
    (s t : Finset (Fin (Fintype.card
      (PrebananaAbstractAtoms (AsBoolAlg α))))) :
    (folkmanNativeFiniteRingCodeEquiv α).symm (symmDiff s t) =
      (folkmanNativeFiniteRingCodeEquiv α).symm s +
        (folkmanNativeFiniteRingCodeEquiv α).symm t := by
  classical
  let e := folkmanNativeFiniteRingCodeEquiv α
  apply e.injective
  change e (e.symm (symmDiff s t)) =
    e (e.symm s + e.symm t)
  rw [e.apply_symm_apply, folkmanNativeFiniteRingCode_add,
    e.apply_symm_apply, e.apply_symm_apply]

/-- Inverse coding respects intersection. -/
theorem folkmanNativeFiniteRingCode_symm_mul
    (α : Type*) [BooleanRing α] [Fintype α]
    (s t : Finset (Fin (Fintype.card
      (PrebananaAbstractAtoms (AsBoolAlg α))))) :
    (folkmanNativeFiniteRingCodeEquiv α).symm (s ∩ t) =
      (folkmanNativeFiniteRingCodeEquiv α).symm s *
        (folkmanNativeFiniteRingCodeEquiv α).symm t := by
  classical
  let e := folkmanNativeFiniteRingCodeEquiv α
  apply e.injective
  change e (e.symm (s ∩ t)) =
    e (e.symm s * e.symm t)
  rw [e.apply_symm_apply, folkmanNativeFiniteRingCode_mul,
    e.apply_symm_apply, e.apply_symm_apply]

/-- Conjugate a native, possibly non-unital, Boolean-ring homomorphism
by the finite-index ring equivalences. -/
noncomputable def folkmanNativeFinRingMap
    {α β : Type*}
    [BooleanRing α] [Fintype α]
    [BooleanRing β] [Fintype β]
    (f : α →ₙ+* β) :
    Finset (Fin (Fintype.card (PrebananaAbstractAtoms (AsBoolAlg α)))) →
      Finset (Fin (Fintype.card (PrebananaAbstractAtoms (AsBoolAlg β)))) :=
  fun s => folkmanNativeFiniteRingCodeEquiv β
    (f ((folkmanNativeFiniteRingCodeEquiv α).symm s))

/-- The original ring map and its finite-index conjugate commute. -/
theorem folkmanNativeFinRingMap_apply
    {α β : Type*}
    [BooleanRing α] [Fintype α]
    [BooleanRing β] [Fintype β]
    (f : α →ₙ+* β) (x : α) :
    folkmanNativeFinRingMap f
      (folkmanNativeFiniteRingCodeEquiv α x) =
        folkmanNativeFiniteRingCodeEquiv β (f x) := by
  simp [folkmanNativeFinRingMap]

theorem folkmanNativeFinRingMap_zero
    {α β : Type*}
    [BooleanRing α] [Fintype α]
    [BooleanRing β] [Fintype β]
    (f : α →ₙ+* β) :
    folkmanNativeFinRingMap f ∅ = ∅ := by
  classical
  change folkmanNativeFiniteRingCodeEquiv β
    (f ((folkmanNativeFiniteRingCodeEquiv α).symm ∅)) = ∅
  rw [folkmanNativeFiniteRingCode_symm_zero, map_zero,
    folkmanNativeFiniteRingCode_zero]

theorem folkmanNativeFinRingMap_add
    {α β : Type*}
    [BooleanRing α] [Fintype α]
    [BooleanRing β] [Fintype β]
    (f : α →ₙ+* β)
    (s t : Finset (Fin (Fintype.card
      (PrebananaAbstractAtoms (AsBoolAlg α))))) :
    folkmanNativeFinRingMap f (symmDiff s t) =
      symmDiff (folkmanNativeFinRingMap f s)
        (folkmanNativeFinRingMap f t) := by
  classical
  change folkmanNativeFiniteRingCodeEquiv β
      (f ((folkmanNativeFiniteRingCodeEquiv α).symm (symmDiff s t))) =
    symmDiff
      (folkmanNativeFiniteRingCodeEquiv β
        (f ((folkmanNativeFiniteRingCodeEquiv α).symm s)))
      (folkmanNativeFiniteRingCodeEquiv β
        (f ((folkmanNativeFiniteRingCodeEquiv α).symm t)))
  rw [folkmanNativeFiniteRingCode_symm_add, map_add,
    folkmanNativeFiniteRingCode_add]

theorem folkmanNativeFinRingMap_mul
    {α β : Type*}
    [BooleanRing α] [Fintype α]
    [BooleanRing β] [Fintype β]
    (f : α →ₙ+* β)
    (s t : Finset (Fin (Fintype.card
      (PrebananaAbstractAtoms (AsBoolAlg α))))) :
    folkmanNativeFinRingMap f (s ∩ t) =
      folkmanNativeFinRingMap f s ∩
        folkmanNativeFinRingMap f t := by
  classical
  change folkmanNativeFiniteRingCodeEquiv β
      (f ((folkmanNativeFiniteRingCodeEquiv α).symm (s ∩ t))) =
    folkmanNativeFiniteRingCodeEquiv β
      (f ((folkmanNativeFiniteRingCodeEquiv α).symm s)) ∩
    folkmanNativeFiniteRingCodeEquiv β
      (f ((folkmanNativeFiniteRingCodeEquiv α).symm t))
  rw [folkmanNativeFiniteRingCode_symm_mul, map_mul,
    folkmanNativeFiniteRingCode_mul]

theorem folkmanNativeFinRingMap_injective
    {α β : Type*}
    [BooleanRing α] [Fintype α]
    [BooleanRing β] [Fintype β]
    (f : α →ₙ+* β) (hf : Function.Injective f) :
    Function.Injective (folkmanNativeFinRingMap f) := by
  intro s t h
  apply (folkmanNativeFiniteRingCodeEquiv α).symm.injective
  apply hf
  apply (folkmanNativeFiniteRingCodeEquiv β).injective
  exact h

/-- Pairing-preserving native embeddings remain pairing-preserving
after both sorts have been reindexed.  This is a statement for ALL
finite support subsets, not just singleton atoms. -/
theorem folkmanNativeFinRingMaps_preserve_pairing
    {AL AR BL BR : Type*}
    [BooleanRing AL] [Fintype AL]
    [BooleanRing AR] [Fintype AR]
    [BooleanRing BL] [Fintype BL]
    [BooleanRing BR] [Fintype BR]
    (fL : AL →ₙ+* BL) (fR : AR →ₙ+* BR)
    (γA : AL → AR → F2) (γB : BL → BR → F2)
    (hAleft : ∀ x x' y, γA (x + x') y = γA x y + γA x' y)
    (hAright : ∀ x y y', γA x (y + y') = γA x y + γA x y')
    (hBleft : ∀ x x' y, γB (x + x') y = γB x y + γB x' y)
    (hBright : ∀ x y y', γB x (y + y') = γB x y + γB x y')
    (hcompat : ∀ x y, γB (fL x) (fR y) = γA x y)
    (s : Finset (Fin (Fintype.card
      (PrebananaAbstractAtoms (AsBoolAlg AL)))))
    (t : Finset (Fin (Fintype.card
      (PrebananaAbstractAtoms (AsBoolAlg AR))))) :
    (∑ i ∈ folkmanNativeFinRingMap fL s,
      ∑ j ∈ folkmanNativeFinRingMap fR t,
        (folkmanNativeFinCode γB).edge i j) =
      ∑ i ∈ s, ∑ j ∈ t, (folkmanNativeFinCode γA).edge i j := by
  classical
  let x : AL := (folkmanNativeFiniteRingCodeEquiv AL).symm s
  let y : AR := (folkmanNativeFiniteRingCodeEquiv AR).symm t
  have hx : folkmanNativeFiniteRingCodeEquiv AL x = s :=
    (folkmanNativeFiniteRingCodeEquiv AL).apply_symm_apply s
  have hy : folkmanNativeFiniteRingCodeEquiv AR y = t :=
    (folkmanNativeFiniteRingCodeEquiv AR).apply_symm_apply t
  have hfl :
      folkmanNativeFinRingMap fL s =
        folkmanNativeFiniteRingCodeEquiv BL (fL x) := by
    rfl
  have hfr :
      folkmanNativeFinRingMap fR t =
        folkmanNativeFiniteRingCodeEquiv BR (fR y) := by
    rfl
  calc
    (∑ i ∈ folkmanNativeFinRingMap fL s,
      ∑ j ∈ folkmanNativeFinRingMap fR t,
        (folkmanNativeFinCode γB).edge i j) =
      ∑ i ∈ folkmanNativeFiniteRingCodeEquiv BL (fL x),
        ∑ j ∈ folkmanNativeFiniteRingCodeEquiv BR (fR y),
          (folkmanNativeFinCode γB).edge i j := by
            rw [hfl, hfr]
    _ = γB (fL x) (fR y) :=
      (folkmanNativeFinCode_pairing γB hBleft hBright (fL x) (fR y)).symm
    _ = γA x y := hcompat x y
    _ = ∑ i ∈ folkmanNativeFiniteRingCodeEquiv AL x,
      ∑ j ∈ folkmanNativeFiniteRingCodeEquiv AR y,
        (folkmanNativeFinCode γA).edge i j :=
          folkmanNativeFinCode_pairing γA hAleft hAright x y
    _ = ∑ i ∈ s, ∑ j ∈ t,
      (folkmanNativeFinCode γA).edge i j := by rw [hx, hy]

end SuccessorTree.NonPrecompact
