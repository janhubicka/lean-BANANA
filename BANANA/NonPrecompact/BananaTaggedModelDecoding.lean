import BANANA.NonPrecompact.BananaLimitFirstOrder
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The two-sorted structure of arbitrary tagged BANANA models

Every finite set in a model of the complete tagged theory belongs to a
countable elementary submodel. Countable categoricity makes that submodel a
copy of the concrete tagged pairing. The resulting local elementary embeddings
transport the vector space and pairing laws to arbitrary tagged models.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder Cardinal

private def bananaTaggedRelationCode {n} : BananaTaggedRelation n → Fin 7
  | .left => 0
  | .right => 1
  | .leftZero => 2
  | .rightZero => 3
  | .leftAdd => 4
  | .rightAdd => 5
  | .edge => 6

private theorem bananaTagged_card_le_aleph0 : bananaTaggedLanguage.card ≤ ℵ₀ := by
  have (n : ℕ) : Countable (bananaTaggedLanguage.Relations n) :=
    Function.Injective.countable (f := bananaTaggedRelationCode) (by
      intro a b h
      cases a <;> cases b <;> first | rfl | contradiction)
  exact Cardinal.mk_le_aleph0_iff.mpr (by
    change Countable ((Σ n : ℕ, Empty) ⊕ (Σ n : ℕ, bananaTaggedLanguage.Relations n))
    infer_instance)

private theorem bananaTagged_elementarilyEquivalent (M : Type*) [bananaTaggedLanguage.Structure M]
    [M ⊨ bananaTaggedLanguage.completeTheory BananaTaggedCarrier] :
    BananaTaggedCarrier ≅[bananaTaggedLanguage] M :=
  Language.elementarilyEquivalent_iff.mpr fun φ =>
    (Language.realize_iff_of_model_completeTheory BananaTaggedCarrier M φ).symm

/-- Every finite subset of a model of the tagged theory lies in the image of an
elementary embedding of the concrete tagged limit. -/
theorem exists_bananaTagged_elementaryEmbedding_covering
    (M : Type*) [bananaTaggedLanguage.Structure M]
    [M ⊨ bananaTaggedLanguage.completeTheory BananaTaggedCarrier]
    (s : Set M) (hs : s.Finite) :
    ∃ f : BananaTaggedCarrier ↪ₑ[bananaTaggedLanguage] M, s ⊆ Set.range f := by
  have hM := bananaTagged_elementarilyEquivalent M
  have hInf : Infinite M := hM.infinite_iff.mp (Cardinal.aleph0_le_mk_iff.mp bananaTaggedCarrier_card.ge)
  let := hs.fintype
  obtain ⟨S, hsS, hS⟩ := bananaTaggedLanguage.exists_elementarySubstructure_card_eq s (ℵ₀ : Cardinal.{0})
    le_rfl (by simp) (by simpa using bananaTagged_card_le_aleph0) (by simp)
  have hS' : Cardinal.mk S = ℵ₀ := by simpa using hS
  have : Countable S := Cardinal.mk_le_aleph0_iff.mp hS'.le
  have : Nonempty S := Cardinal.mk_ne_zero_iff.mp (hS' ▸ Cardinal.aleph0_ne_zero)
  have hSTh := hM.trans S.subtype.elementarilyEquivalent.symm
  obtain ⟨e⟩ := nonempty_equiv_of_finite_formula_type_covers
    (show BananaTaggedCarrier ≅[bananaTaggedLanguage] BananaTaggedCarrier from rfl) hSTh (fun n => by
      obtain ⟨R, hR⟩ := bananaLimit_firstOrder_finite_tuple_orbit_representatives n
      exact ⟨R, formula_type_cover_of_finset_automorphism_orbit_representatives R hR⟩)
  refine ⟨S.subtype.comp e.toElementaryEmbedding, ?_⟩
  intro x hx
  exact ⟨e.symm ⟨x, hsS hx⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩

/-- The left and right vector sorts of the BANANA pairing. -/
inductive BananaSort where
  | left
  | right

namespace BananaSort

private def sortSymbol : BananaSort → BananaTaggedRelation 1
  | .left => .left
  | .right => .right

private def zeroSymbol : BananaSort → BananaTaggedRelation 1
  | .left => .leftZero
  | .right => .rightZero

private def addSymbol : BananaSort → BananaTaggedRelation 3
  | .left => .leftAdd
  | .right => .rightAdd

private def tag : BananaSort → BananaLimitVector → BananaTaggedCarrier
  | .left => Sum.inl
  | .right => Sum.inr

private theorem tag_injective (s : BananaSort) : Function.Injective s.tag := by
  cases s
  · exact Sum.inl_injective
  · exact Sum.inr_injective

variable {M : Type*} [bananaTaggedLanguage.Structure M]

private def hasSort (s : BananaSort) (x : M) : Prop :=
  Language.Structure.RelMap (L := bananaTaggedLanguage) s.sortSymbol ![x]

private def hasZero (s : BananaSort) (x : M) : Prop :=
  Language.Structure.RelMap (L := bananaTaggedLanguage) s.zeroSymbol ![x]

private def hasAdd (s : BananaSort) (x y z : M) : Prop :=
  Language.Structure.RelMap (L := bananaTaggedLanguage) s.addSymbol ![x, y, z]

/-- The carrier defined by one of the two sort predicates. -/
def Carrier (s : BananaSort) (M : Type*) [bananaTaggedLanguage.Structure M] :=
  {x : M // s.hasSort x}

private theorem native_hasSort (s : BananaSort) (a : BananaTaggedCarrier) :
    s.hasSort a ↔ ∃ x, a = s.tag x := by
  cases s <;> cases a <;> (first | change True ↔ _ | change False ↔ _) <;> simp [tag]

private theorem native_hasZero (s : BananaSort) (a : BananaTaggedCarrier) :
    s.hasZero a ↔ a = s.tag 0 := by
  cases s <;> rfl

private theorem native_hasAdd (s : BananaSort) (a b c : BananaTaggedCarrier) :
    s.hasAdd a b c ↔ ∃ x y, a = s.tag x ∧ b = s.tag y ∧ c = s.tag (x + y) := by
  cases s <;> cases a <;> cases b <;> cases c <;>
    first
    | change False ↔ _
      simp [tag]
    | rename_i u v w
      change u + v = w ↔ _
      simp [tag, eq_comm]

private theorem map_hasSort (f : BananaTaggedCarrier ↪ₑ[bananaTaggedLanguage] M)
    (s : BananaSort) (a : BananaTaggedCarrier) : s.hasSort (f a) ↔ s.hasSort a := by
  have h : f ∘ ![a] = ![f a] := by ext i; fin_cases i; rfl
  simpa only [hasSort, h] using f.map_rel s.sortSymbol ![a]

private theorem map_hasZero (f : BananaTaggedCarrier ↪ₑ[bananaTaggedLanguage] M)
    (s : BananaSort) (a : BananaTaggedCarrier) : s.hasZero (f a) ↔ s.hasZero a := by
  have h : f ∘ ![a] = ![f a] := by ext i; fin_cases i; rfl
  simpa only [hasZero, h] using f.map_rel s.zeroSymbol ![a]

private theorem map_hasAdd (f : BananaTaggedCarrier ↪ₑ[bananaTaggedLanguage] M)
    (s : BananaSort) (a b c : BananaTaggedCarrier) :
    s.hasAdd (f a) (f b) (f c) ↔ s.hasAdd a b c := by
  have h : f ∘ ![a, b, c] = ![f a, f b, f c] := by ext i; fin_cases i <;> rfl
  simpa only [hasAdd, h] using f.map_rel s.addSymbol ![a, b, c]

private def nativeMap (f : BananaTaggedCarrier ↪ₑ[bananaTaggedLanguage] M)
    (s : BananaSort) (v : BananaLimitVector) : s.Carrier M :=
  ⟨f (s.tag v), (map_hasSort f s _).mpr ((native_hasSort s _).mpr ⟨v, rfl⟩)⟩

private theorem exists_nativeMap_preimage (f : BananaTaggedCarrier ↪ₑ[bananaTaggedLanguage] M)
    (s : BananaSort) (x : s.Carrier M) (hx : x.val ∈ Set.range f) :
    ∃ v, nativeMap f s v = x := by
  obtain ⟨a, ha⟩ := hx
  have hsort : s.hasSort (f a) := ha.symm ▸ x.property
  obtain ⟨v, hv⟩ := (native_hasSort s a).mp ((map_hasSort f s a).mp hsort)
  refine ⟨v, Subtype.ext ?_⟩
  exact (congrArg f hv).symm.trans ha

private theorem hasZero_nativeMap (f : BananaTaggedCarrier ↪ₑ[bananaTaggedLanguage] M)
    (s : BananaSort) : s.hasZero (nativeMap f s 0).val :=
  (map_hasZero f s _).mpr ((native_hasZero s _).mpr rfl)

private theorem hasAdd_nativeMap (f : BananaTaggedCarrier ↪ₑ[bananaTaggedLanguage] M)
    (s : BananaSort) (x y : BananaLimitVector) :
    s.hasAdd (nativeMap f s x).val (nativeMap f s y).val (nativeMap f s (x + y)).val :=
  (map_hasAdd f s _ _ _).mpr ((native_hasAdd s _ _ _).mpr ⟨x, y, rfl, rfl, rfl⟩)

variable [M ⊨ bananaTaggedLanguage.completeTheory BananaTaggedCarrier]

private theorem hasZero_exists (s : BananaSort) : ∃ x : s.Carrier M, s.hasZero x.val := by
  obtain ⟨f, _⟩ := exists_bananaTagged_elementaryEmbedding_covering M ∅ Set.finite_empty
  exact ⟨nativeMap f s 0, hasZero_nativeMap f s⟩

private theorem hasZero_unique (s : BananaSort) {x y : M} (hx : s.hasZero x) (hy : s.hasZero y) :
    x = y := by
  obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {x, y} (by simp)
  obtain ⟨a, rfl⟩ := hf (show x ∈ ({x, y} : Set M) by simp)
  obtain ⟨b, rfl⟩ := hf (show y ∈ ({f a, y} : Set M) by simp)
  have ha := (native_hasZero s a).mp ((map_hasZero f s a).mp hx)
  have hb := (native_hasZero s b).mp ((map_hasZero f s b).mp hy)
  rw [ha, hb]

private theorem hasAdd_exists (s : BananaSort) (x y : s.Carrier M) :
    ∃ z : s.Carrier M, s.hasAdd x.val y.val z.val := by
  obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {x.val, y.val} (by simp)
  obtain ⟨a, rfl⟩ := exists_nativeMap_preimage f s x (hf (by simp))
  obtain ⟨b, rfl⟩ := exists_nativeMap_preimage f s y (hf (by simp))
  exact ⟨nativeMap f s (a + b), hasAdd_nativeMap f s a b⟩

private theorem hasAdd_unique (s : BananaSort) {x y z w : M}
    (hz : s.hasAdd x y z) (hw : s.hasAdd x y w) : z = w := by
  obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {x, y, z, w} (by simp)
  obtain ⟨a, rfl⟩ := hf (show x ∈ ({x, y, z, w} : Set M) by simp)
  obtain ⟨b, rfl⟩ := hf (show y ∈ ({f a, y, z, w} : Set M) by simp)
  obtain ⟨c, rfl⟩ := hf (show z ∈ ({f a, f b, z, w} : Set M) by simp)
  obtain ⟨d, rfl⟩ := hf (show w ∈ ({f a, f b, f c, w} : Set M) by simp)
  obtain ⟨u, v, rfl, rfl, rfl⟩ := (native_hasAdd s a b c).mp ((map_hasAdd f s a b c).mp hz)
  obtain ⟨u', v', hu, hv, rfl⟩ := (native_hasAdd s _ _ d).mp ((map_hasAdd f s _ _ d).mp hw)
  rw [s.tag_injective hu, s.tag_injective hv]

private noncomputable def zero (s : BananaSort) : s.Carrier M :=
  (hasZero_exists s).choose

private noncomputable def add (s : BananaSort) (x y : s.Carrier M) : s.Carrier M :=
  (hasAdd_exists s x y).choose

private theorem nativeMap_zero (f : BananaTaggedCarrier ↪ₑ[bananaTaggedLanguage] M)
    (s : BananaSort) : nativeMap f s 0 = s.zero :=
  Subtype.ext (hasZero_unique s (hasZero_nativeMap f s) (hasZero_exists s).choose_spec)

private theorem nativeMap_add (f : BananaTaggedCarrier ↪ₑ[bananaTaggedLanguage] M)
    (s : BananaSort) (x y : BananaLimitVector) :
    nativeMap f s (x + y) = s.add (nativeMap f s x) (nativeMap f s y) :=
  Subtype.ext (hasAdd_unique s (hasAdd_nativeMap f s x y) (hasAdd_exists s _ _).choose_spec)

noncomputable instance carrierZero (s : BananaSort) : Zero (s.Carrier M) := ⟨s.zero⟩

noncomputable instance carrierAdd (s : BananaSort) : Add (s.Carrier M) := ⟨s.add⟩

/-- The vector addition and zero of a sort, recovered from their graphs. -/
noncomputable instance carrierAddCommMonoid (s : BananaSort) : AddCommMonoid (s.Carrier M) where
  zero := s.zero
  add := s.add
  nsmul := nsmulRec
  zero_add x := by
    change s.add s.zero x = x
    obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {x.val} (by simp)
    obtain ⟨a, rfl⟩ := exists_nativeMap_preimage f s x (hf (by simp))
    rw [← nativeMap_zero f s, ← nativeMap_add, zero_add]
  add_zero x := by
    change s.add x s.zero = x
    obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {x.val} (by simp)
    obtain ⟨a, rfl⟩ := exists_nativeMap_preimage f s x (hf (by simp))
    rw [← nativeMap_zero f s, ← nativeMap_add, add_zero]
  add_comm x y := by
    change s.add x y = s.add y x
    obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {x.val, y.val} (by simp)
    obtain ⟨a, rfl⟩ := exists_nativeMap_preimage f s x (hf (by simp))
    obtain ⟨b, rfl⟩ := exists_nativeMap_preimage f s y (hf (by simp))
    rw [← nativeMap_add, ← nativeMap_add, add_comm a b]
  add_assoc x y z := by
    change s.add (s.add x y) z = s.add x (s.add y z)
    obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {x.val, y.val, z.val} (by simp)
    obtain ⟨a, rfl⟩ := exists_nativeMap_preimage f s x (hf (by simp))
    obtain ⟨b, rfl⟩ := exists_nativeMap_preimage f s y (hf (by simp))
    obtain ⟨c, rfl⟩ := exists_nativeMap_preimage f s z (hf (by simp))
    simp only [← nativeMap_add, add_assoc]

/-- Each of the reconstructed vector sorts has characteristic two. -/
noncomputable instance carrierModule (s : BananaSort) : Module F2 (s.Carrier M) :=
  AddCommMonoid.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {x.val} (by simp)
    obtain ⟨a, rfl⟩ := exists_nativeMap_preimage f s x (hf (by simp))
    change s.add (nativeMap f s a) (nativeMap f s a) = s.zero
    rw [← nativeMap_add, ZModModule.add_self, nativeMap_zero]

noncomputable instance carrierAddCommGroup (s : BananaSort) : AddCommGroup (s.Carrier M) :=
  Module.addCommMonoidToAddCommGroup F2

private theorem hasZero_iff (s : BananaSort) (x : M) :
    s.hasZero x ↔ x = (0 : s.Carrier M).val := by
  have h := (hasZero_exists (M := M) s).choose_spec
  exact ⟨fun hx => hasZero_unique s hx h, fun hx => hx.symm ▸ h⟩

private theorem hasAdd_iff (s : BananaSort) (x y z : M) :
    s.hasAdd x y z ↔ ∃ a b : s.Carrier M, x = a.val ∧ y = b.val ∧ z = (a + b).val := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {x, y, z} (by simp)
    obtain ⟨a, rfl⟩ := hf (show x ∈ ({x, y, z} : Set M) by simp)
    obtain ⟨b, rfl⟩ := hf (show y ∈ ({f a, y, z} : Set M) by simp)
    obtain ⟨c, rfl⟩ := hf (show z ∈ ({f a, f b, z} : Set M) by simp)
    obtain ⟨u, v, rfl, rfl, rfl⟩ := (native_hasAdd s a b c).mp ((map_hasAdd f s a b c).mp h)
    exact ⟨nativeMap f s u, nativeMap f s v, rfl, rfl, congrArg Subtype.val (nativeMap_add f s u v)⟩
  · rintro ⟨a, b, rfl, rfl, rfl⟩
    exact (hasAdd_exists s a b).choose_spec

end BananaSort

private def bananaTaggedHasEdge {M : Type*} [bananaTaggedLanguage.Structure M]
    (x y : M) : Prop :=
  Language.Structure.RelMap (L := bananaTaggedLanguage) .edge ![x, y]

private theorem native_bananaTaggedHasEdge (a b : BananaTaggedCarrier) :
    bananaTaggedHasEdge a b ↔
      ∃ x y, a = Sum.inl x ∧ b = Sum.inr y ∧ bananaLimitPairing x y = 1 := by
  cases a <;> cases b <;>
    first
    | change False ↔ _
      simp
    | rename_i x y
      change bananaLimitPairing x y = 1 ↔ _
      simp

private theorem map_bananaTaggedHasEdge {M : Type*} [bananaTaggedLanguage.Structure M]
    (f : BananaTaggedCarrier ↪ₑ[bananaTaggedLanguage] M) (a b : BananaTaggedCarrier) :
    bananaTaggedHasEdge (f a) (f b) ↔ bananaTaggedHasEdge a b := by
  have h : f ∘ ![a, b] = ![f a, f b] := by ext i; fin_cases i <;> rfl
  simpa only [bananaTaggedHasEdge, h] using f.map_rel BananaTaggedRelation.edge ![a, b]

variable {M : Type*} [bananaTaggedLanguage.Structure M]
variable [M ⊨ bananaTaggedLanguage.completeTheory BananaTaggedCarrier]

private noncomputable def bananaTaggedModelPairBit
    (x : BananaSort.left.Carrier M) (y : BananaSort.right.Carrier M) : F2 := by
  classical
  exact if bananaTaggedHasEdge x.val y.val then 1 else 0

omit [M ⊨ bananaTaggedLanguage.completeTheory BananaTaggedCarrier] in
private theorem bananaTaggedModelPairBit_of_nativeMap
    (f : BananaTaggedCarrier ↪ₑ[bananaTaggedLanguage] M) (x y : BananaLimitVector) :
    bananaTaggedModelPairBit (BananaSort.nativeMap f .left x) (BananaSort.nativeMap f .right y) =
      bananaLimitPairing x y := by
  have hEdge : bananaTaggedHasEdge (f (Sum.inl x)) (f (Sum.inr y)) ↔ bananaLimitPairing x y = 1 :=
    map_bananaTaggedHasEdge f _ _
  classical
  change (if bananaTaggedHasEdge (f (Sum.inl x)) (f (Sum.inr y)) then 1 else 0) = _
  rw [hEdge]
  rcases f2_eq_zero_or_one (bananaLimitPairing x y) with h | h <;> simp [h]

private theorem bananaTaggedModelPairBit_zero_left (y : BananaSort.right.Carrier M) :
    bananaTaggedModelPairBit 0 y = 0 := by
  obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {y.val} (by simp)
  obtain ⟨v, rfl⟩ := BananaSort.exists_nativeMap_preimage f .right y (hf (by simp))
  change bananaTaggedModelPairBit BananaSort.left.zero _ = _
  rw [← BananaSort.nativeMap_zero f .left, bananaTaggedModelPairBit_of_nativeMap]
  exact bananaLimitPairing_zero_left _

private theorem bananaTaggedModelPairBit_zero_right (x : BananaSort.left.Carrier M) :
    bananaTaggedModelPairBit x 0 = 0 := by
  obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {x.val} (by simp)
  obtain ⟨u, rfl⟩ := BananaSort.exists_nativeMap_preimage f .left x (hf (by simp))
  change bananaTaggedModelPairBit _ BananaSort.right.zero = _
  rw [← BananaSort.nativeMap_zero f .right, bananaTaggedModelPairBit_of_nativeMap]
  exact bananaLimitPairing_zero_right _

private theorem bananaTaggedModelPairBit_add_left
    (x x' : BananaSort.left.Carrier M) (y : BananaSort.right.Carrier M) :
    bananaTaggedModelPairBit (x + x') y =
      bananaTaggedModelPairBit x y + bananaTaggedModelPairBit x' y := by
  obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {x.val, x'.val, y.val} (by simp)
  obtain ⟨u, rfl⟩ := BananaSort.exists_nativeMap_preimage f .left x (hf (by simp))
  obtain ⟨u', rfl⟩ := BananaSort.exists_nativeMap_preimage f .left x' (hf (by simp))
  obtain ⟨v, rfl⟩ := BananaSort.exists_nativeMap_preimage f .right y (hf (by simp))
  change bananaTaggedModelPairBit (BananaSort.left.add _ _) _ = _
  simp only [← BananaSort.nativeMap_add, bananaTaggedModelPairBit_of_nativeMap, bananaLimitPairing_add_left]

private theorem bananaTaggedModelPairBit_add_right
    (x : BananaSort.left.Carrier M) (y y' : BananaSort.right.Carrier M) :
    bananaTaggedModelPairBit x (y + y') =
      bananaTaggedModelPairBit x y + bananaTaggedModelPairBit x y' := by
  obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {x.val, y.val, y'.val} (by simp)
  obtain ⟨u, rfl⟩ := BananaSort.exists_nativeMap_preimage f .left x (hf (by simp))
  obtain ⟨v, rfl⟩ := BananaSort.exists_nativeMap_preimage f .right y (hf (by simp))
  obtain ⟨v', rfl⟩ := BananaSort.exists_nativeMap_preimage f .right y' (hf (by simp))
  change bananaTaggedModelPairBit _ (BananaSort.right.add _ _) = _
  simp only [← BananaSort.nativeMap_add, bananaTaggedModelPairBit_of_nativeMap, bananaLimitPairing_add_right]

/-- The pairing in an arbitrary model of the complete tagged BANANA theory.
Its value is one exactly when the tagged edge relation holds. -/
noncomputable def bananaTaggedModelPairing :
    BananaSort.left.Carrier M →ₗ[F2] BananaSort.right.Carrier M →ₗ[F2] F2 :=
  LinearMap.mk₂ F2 bananaTaggedModelPairBit bananaTaggedModelPairBit_add_left
    (fun c x y => by
      rcases f2_eq_zero_or_one c with rfl | rfl <;> simp [bananaTaggedModelPairBit_zero_left])
    bananaTaggedModelPairBit_add_right
    (fun c x y => by
      rcases f2_eq_zero_or_one c with rfl | rfl <;> simp [bananaTaggedModelPairBit_zero_right])

private theorem bananaTaggedModelPairing_eq_one_iff
    (x : BananaSort.left.Carrier M) (y : BananaSort.right.Carrier M) :
    bananaTaggedModelPairing x y = 1 ↔ bananaTaggedHasEdge x.val y.val := by
  classical
  change (if bananaTaggedHasEdge x.val y.val then (1 : F2) else 0) = 1 ↔ _
  split <;> simp [*]

private theorem bananaTaggedHasEdge_iff (x y : M) :
    bananaTaggedHasEdge x y ↔ ∃ a : BananaSort.left.Carrier M, ∃ b : BananaSort.right.Carrier M,
      x = a.val ∧ y = b.val ∧ bananaTaggedModelPairing a b = 1 := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {x, y} (by simp)
    obtain ⟨a, rfl⟩ := hf (show x ∈ ({x, y} : Set M) by simp)
    obtain ⟨b, rfl⟩ := hf (show y ∈ ({f a, y} : Set M) by simp)
    obtain ⟨u, v, rfl, rfl, _⟩ := (native_bananaTaggedHasEdge a b).mp
      ((map_bananaTaggedHasEdge f a b).mp h)
    refine ⟨BananaSort.nativeMap f .left u, BananaSort.nativeMap f .right v, rfl, rfl, ?_⟩
    exact (bananaTaggedModelPairing_eq_one_iff _ _).mpr h
  · rintro ⟨a, b, rfl, rfl, h⟩
    exact (bananaTaggedModelPairing_eq_one_iff a b).mp h

private theorem bananaTaggedSort_partition (x : M) :
    BananaSort.left.hasSort x ↔ ¬ BananaSort.right.hasSort x := by
  obtain ⟨f, hf⟩ := exists_bananaTagged_elementaryEmbedding_covering M {x} (by simp)
  obtain ⟨a, rfl⟩ := hf (show x ∈ ({x} : Set M) by simp)
  rw [BananaSort.map_hasSort f .left, BananaSort.map_hasSort f .right]
  cases a
  · change True ↔ ¬ False
    simp
  · change False ↔ ¬ True
    simp

private noncomputable def bananaTaggedModelUntag :
    BananaSort.left.Carrier M ⊕ BananaSort.right.Carrier M ≃ M := by
  refine Equiv.ofBijective (Sum.elim Subtype.val Subtype.val) ⟨?_, ?_⟩
  · intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext h)
      | inr y =>
        change x.val = y.val at h
        exact False.elim ((bananaTaggedSort_partition _).mp x.property (h.symm ▸ y.property))
    | inr x =>
      cases y with
      | inl y =>
        change x.val = y.val at h
        exact False.elim ((bananaTaggedSort_partition _).mp y.property (h ▸ x.property))
      | inr y => exact congrArg Sum.inr (Subtype.ext h)
  · intro x
    classical
    by_cases h : BananaSort.right.hasSort x
    · exact ⟨Sum.inr ⟨x, h⟩, rfl⟩
    · exact ⟨Sum.inl ⟨x, (bananaTaggedSort_partition x).mpr h⟩, rfl⟩

private theorem bananaTaggedModelUntag_inl (x : BananaSort.left.Carrier M) :
    bananaTaggedModelUntag (Sum.inl x) = x.val := rfl

private theorem bananaTaggedModelUntag_inr (x : BananaSort.right.Carrier M) :
    bananaTaggedModelUntag (Sum.inr x) = x.val := rfl

/-- Tag two vector sorts, recording zero and addition by their graphs and
marking the pairs whose bit is one. -/
@[instance_reducible] def bananaTaggedPairingStructure {L R : Type*} [Zero L] [Zero R] [Add L] [Add R]
    (pair : L → R → F2) : bananaTaggedLanguage.Structure (L ⊕ R) where
  funMap f := Empty.elim f
  RelMap {_} rel a := match rel with
    | .left => ∃ x, a 0 = Sum.inl x
    | .right => ∃ y, a 0 = Sum.inr y
    | .leftZero => a 0 = Sum.inl 0
    | .rightZero => a 0 = Sum.inr 0
    | .leftAdd => ∃ x y, a 0 = Sum.inl x ∧ a 1 = Sum.inl y ∧ a 2 = Sum.inl (x + y)
    | .rightAdd => ∃ x y, a 0 = Sum.inr x ∧ a 1 = Sum.inr y ∧ a 2 = Sum.inr (x + y)
    | .edge => ∃ x y, a 0 = Sum.inl x ∧ a 1 = Sum.inr y ∧ pair x y = 1

/-- The generic tagged construction applied to the concrete pairing agrees
with the original first-order BANANA limit via the identity on the carrier. -/
def bananaTaggedNativePairingEquiv :
    @Language.Equiv bananaTaggedLanguage BananaTaggedCarrier BananaTaggedCarrier
      (bananaTaggedPairingStructure bananaLimitPairing) bananaTaggedStructure := by
  refine @Language.Equiv.mk bananaTaggedLanguage BananaTaggedCarrier BananaTaggedCarrier
    (bananaTaggedPairingStructure bananaLimitPairing) bananaTaggedStructure (Equiv.refl _)
    (fun f _ => Empty.elim f) ?_
  intro n r a
  cases r with
  | left => exact BananaSort.native_hasSort .left (a 0)
  | right => exact BananaSort.native_hasSort .right (a 0)
  | leftZero => rfl
  | rightZero => rfl
  | leftAdd => exact BananaSort.native_hasAdd .left (a 0) (a 1) (a 2)
  | rightAdd => exact BananaSort.native_hasAdd .right (a 0) (a 1) (a 2)
  | edge => exact native_bananaTaggedHasEdge (a 0) (a 1)

/-- Decoding an arbitrary model of the complete tagged theory and tagging
its two vector spaces and bilinear pairing again recovers that model,
including all seven relation symbols. -/
noncomputable def bananaTaggedModelPairingEquiv :
    letI := bananaTaggedPairingStructure (fun x y => bananaTaggedModelPairing (M := M) x y)
    (BananaSort.left.Carrier M ⊕ BananaSort.right.Carrier M) ≃[bananaTaggedLanguage] M := by
  letI := bananaTaggedPairingStructure (fun x y => bananaTaggedModelPairing (M := M) x y)
  refine {
    toEquiv := bananaTaggedModelUntag
    map_fun' := fun f _ => Empty.elim f
    map_rel' := ?_ }
  intro n r a
  cases r with
  | left =>
    have ha : bananaTaggedModelUntag.toFun ∘ a = ![bananaTaggedModelUntag (a 0)] := by
      ext i
      fin_cases i
      rfl
    rw [ha]
    change BananaSort.left.hasSort (bananaTaggedModelUntag (a 0)) ↔ ∃ x, a 0 = Sum.inl x
    generalize a 0 = z
    cases z with
    | inl x => exact iff_of_true x.property ⟨x, rfl⟩
    | inr y =>
      have h : ¬ BananaSort.left.hasSort y.val :=
        fun hx => (bananaTaggedSort_partition _).mp hx y.property
      change BananaSort.left.hasSort y.val ↔ _
      simp [h]
  | right =>
    have ha : bananaTaggedModelUntag.toFun ∘ a = ![bananaTaggedModelUntag (a 0)] := by
      ext i
      fin_cases i
      rfl
    rw [ha]
    change BananaSort.right.hasSort (bananaTaggedModelUntag (a 0)) ↔ ∃ y, a 0 = Sum.inr y
    generalize a 0 = z
    cases z with
    | inl x =>
      change BananaSort.right.hasSort x.val ↔ _
      simp [(bananaTaggedSort_partition _).mp x.property]
    | inr y => exact iff_of_true y.property ⟨y, rfl⟩
  | leftZero =>
    have ha : bananaTaggedModelUntag.toFun ∘ a = ![bananaTaggedModelUntag (a 0)] := by
      ext i
      fin_cases i
      rfl
    rw [ha]
    change BananaSort.left.hasZero (bananaTaggedModelUntag (a 0)) ↔ a 0 = Sum.inl 0
    rw [BananaSort.hasZero_iff, ← bananaTaggedModelUntag_inl, Equiv.apply_eq_iff_eq]
  | rightZero =>
    have ha : bananaTaggedModelUntag.toFun ∘ a = ![bananaTaggedModelUntag (a 0)] := by
      ext i
      fin_cases i
      rfl
    rw [ha]
    change BananaSort.right.hasZero (bananaTaggedModelUntag (a 0)) ↔ a 0 = Sum.inr 0
    rw [BananaSort.hasZero_iff, ← bananaTaggedModelUntag_inr, Equiv.apply_eq_iff_eq]
  | leftAdd =>
    have ha : bananaTaggedModelUntag.toFun ∘ a =
      ![bananaTaggedModelUntag (a 0), bananaTaggedModelUntag (a 1), bananaTaggedModelUntag (a 2)] := by
      ext i; fin_cases i <;> rfl
    rw [ha]
    change BananaSort.left.hasAdd (bananaTaggedModelUntag (a 0)) (bananaTaggedModelUntag (a 1))
      (bananaTaggedModelUntag (a 2)) ↔
        ∃ x y, a 0 = Sum.inl x ∧ a 1 = Sum.inl y ∧ a 2 = Sum.inl (x + y)
    simp only [BananaSort.hasAdd_iff, ← bananaTaggedModelUntag_inl, Equiv.apply_eq_iff_eq]
  | rightAdd =>
    have ha : bananaTaggedModelUntag.toFun ∘ a =
      ![bananaTaggedModelUntag (a 0), bananaTaggedModelUntag (a 1), bananaTaggedModelUntag (a 2)] := by
      ext i; fin_cases i <;> rfl
    rw [ha]
    change BananaSort.right.hasAdd (bananaTaggedModelUntag (a 0)) (bananaTaggedModelUntag (a 1))
      (bananaTaggedModelUntag (a 2)) ↔
        ∃ x y, a 0 = Sum.inr x ∧ a 1 = Sum.inr y ∧ a 2 = Sum.inr (x + y)
    simp only [BananaSort.hasAdd_iff, ← bananaTaggedModelUntag_inr, Equiv.apply_eq_iff_eq]
  | edge =>
    have ha : bananaTaggedModelUntag.toFun ∘ a = ![bananaTaggedModelUntag (a 0), bananaTaggedModelUntag (a 1)] := by
      ext i; fin_cases i <;> rfl
    rw [ha]
    change bananaTaggedHasEdge (bananaTaggedModelUntag (a 0)) (bananaTaggedModelUntag (a 1)) ↔
        ∃ x y, a 0 = Sum.inl x ∧ a 1 = Sum.inr y ∧ bananaTaggedModelPairing x y = 1
    rw [bananaTaggedHasEdge_iff]
    constructor
    · rintro ⟨x, y, hx, hy, hp⟩
      exact ⟨x, y, bananaTaggedModelUntag.injective hx, bananaTaggedModelUntag.injective hy, hp⟩
    · rintro ⟨x, y, hx, hy, hp⟩
      exact ⟨x, y, congrArg bananaTaggedModelUntag hx, congrArg bananaTaggedModelUntag hy, hp⟩

end SuccessorTree.NonPrecompact
