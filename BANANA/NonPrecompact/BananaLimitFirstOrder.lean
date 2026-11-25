import BANANA.NonPrecompact.BananaLimitOrbitCoPrecompact
import BANANA.NonPrecompact.FirstOrderOligomorphicCategoricity

/-!
# Countable categoricity of the native BANANA pairing

The two sorts form a disjoint union. The unary predicates record each
sort and its zero. Addition is represented by its graph on each sort,
and the binary relation records the original bit of the pairing.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

/-- The tagged carrier of the original two-sorted BANANA limit. -/
abbrev BananaTaggedCarrier := BananaLimitVector ⊕ BananaLimitVector

/-- Relational encoding of the two sorts, their vector additions and zeroes,
and the original edge relation. -/
inductive BananaTaggedRelation : ℕ → Type
  | left : BananaTaggedRelation 1
  | right : BananaTaggedRelation 1
  | leftZero : BananaTaggedRelation 1
  | rightZero : BananaTaggedRelation 1
  | leftAdd : BananaTaggedRelation 3
  | rightAdd : BananaTaggedRelation 3
  | edge : BananaTaggedRelation 2

def bananaTaggedLanguage : Language where
  Functions _ := Empty
  Relations := BananaTaggedRelation

private abbrev sortLeft : BananaTaggedCarrier → Prop
  | .inl _ => True
  | .inr _ => False

private abbrev sortRight : BananaTaggedCarrier → Prop
  | .inl _ => False
  | .inr _ => True

private abbrev leftAdd : BananaTaggedCarrier → BananaTaggedCarrier → BananaTaggedCarrier → Prop
  | .inl x, .inl y, .inl z => x + y = z
  | _, _, _ => False

private abbrev rightAdd : BananaTaggedCarrier → BananaTaggedCarrier → BananaTaggedCarrier → Prop
  | .inr x, .inr y, .inr z => x + y = z
  | _, _, _ => False

private abbrev edge : BananaTaggedCarrier → BananaTaggedCarrier → Prop
  | .inl x, .inr y => bananaLimitEdge x y
  | _, _ => False

instance bananaTaggedStructure : bananaTaggedLanguage.Structure BananaTaggedCarrier where
  funMap f := Empty.elim f
  RelMap {_} r x := match r with
    | .left => sortLeft (x 0)
    | .right => sortRight (x 0)
    | .leftZero => x 0 = .inl 0
    | .rightZero => x 0 = .inr 0
    | .leftAdd => leftAdd (x 0) (x 1) (x 2)
    | .rightAdd => rightAdd (x 0) (x 1) (x 2)
    | .edge => edge (x 0) (x 1)

/-- Each native automorphism acts on the tagged first-order structure
by exactly its left and right actions. -/
noncomputable def bananaLimit_firstOrderAut (g : BananaLimitAutomorphism) :
    FirstOrderAut bananaTaggedLanguage BananaTaggedCarrier :=
  FirstOrderAut.ofEquiv {
    toEquiv := g.val.1.toEquiv.sumCongr g.val.2.toEquiv
    map_fun' := fun f _ => Empty.elim f
    map_rel' := by
      intro n r x
      have hact : (g.val.1.toEquiv.sumCongr g.val.2.toEquiv).toFun =
          (fun a : BananaTaggedCarrier => g • a) := funext fun a => by cases a <;> rfl
      rw [hact]
      cases r with
      | left =>
        change sortLeft (g • x 0) ↔ sortLeft (x 0)
        cases x 0 <;> rfl
      | right =>
        change sortRight (g • x 0) ↔ sortRight (x 0)
        cases x 0 <;> rfl
      | leftZero =>
        change g • x 0 = Sum.inl 0 ↔ x 0 = Sum.inl 0
        exact (MulAction.injective g).eq_iff' (congrArg Sum.inl g.val.1.map_zero)
      | rightZero =>
        change g • x 0 = Sum.inr 0 ↔ x 0 = Sum.inr 0
        exact (MulAction.injective g).eq_iff' (congrArg Sum.inr g.val.2.map_zero)
      | leftAdd =>
        change leftAdd (g • x 0) (g • x 1) (g • x 2) ↔ leftAdd (x 0) (x 1) (x 2)
        cases x 0 <;> cases x 1 <;> cases x 2 <;> try rfl
        rename_i a b c
        change g.val.1 a + g.val.1 b = g.val.1 c ↔ a + b = c
        rw [← g.val.1.map_add, g.val.1.injective.eq_iff]
      | rightAdd =>
        change rightAdd (g • x 0) (g • x 1) (g • x 2) ↔ rightAdd (x 0) (x 1) (x 2)
        cases x 0 <;> cases x 1 <;> cases x 2 <;> try rfl
        rename_i a b c
        change g.val.2 a + g.val.2 b = g.val.2 c ↔ a + b = c
        rw [← g.val.2.map_add, g.val.2.injective.eq_iff]
      | edge =>
        change edge (g • x 0) (g • x 1) ↔ edge (x 0) (x 1)
        cases x 0 <;> cases x 1 <;> try rfl
        exact iff_of_eq (congrArg (· = 1) (g.property _ _)) }

@[simp] theorem bananaLimit_firstOrderAut_apply
    (g : BananaLimitAutomorphism) (a : BananaTaggedCarrier) :
    (bananaLimit_firstOrderAut g).toEquiv a = g • a := by
  cases a <;> rfl

/-- The known native finite tuple representatives also cover the
automorphism orbits of the relational encoding. -/
theorem bananaLimit_firstOrder_finite_tuple_orbit_representatives (n : ℕ) :
    ∃ R : Finset (Fin n → BananaTaggedCarrier), ∀ x : Fin n → BananaTaggedCarrier,
      ∃ r ∈ R, ∃ g : FirstOrderAut bananaTaggedLanguage BananaTaggedCarrier, g • r = x := by
  obtain ⟨R, hR⟩ := bananaLimit_exists_finite_tagged_tuple_orbit_representatives n
  refine ⟨R, fun x => ?_⟩
  obtain ⟨r, hr, EL, ER, hpair, hacts⟩ := hR x
  let g : BananaLimitAutomorphism := ⟨(EL, ER), hpair⟩
  have hg : g • x = r := funext hacts
  refine ⟨r, hr, bananaLimit_firstOrderAut g⁻¹, funext fun i => ?_⟩
  change (bananaLimit_firstOrderAut g⁻¹).toEquiv (r i) = x i
  rw [bananaLimit_firstOrderAut_apply, ← congrFun hg i]
  exact inv_smul_smul g (x i)

/-- The carrier of this encoding is countably infinite. -/
theorem bananaTaggedCarrier_card : Cardinal.mk BananaTaggedCarrier = Cardinal.aleph0 := by
  let single (q : ℚ) : BananaTaggedCarrier := Sum.inl (Finsupp.single q (1 : F2))
  have hs : Function.Injective single :=
    Sum.inl_injective.comp (Finsupp.single_left_injective one_ne_zero)
  letI : Infinite BananaTaggedCarrier := Infinite.of_injective single hs
  exact Cardinal.mk_eq_aleph0 _

/-- The relational encoding of the native BANANA limit is countably
categorical. -/
theorem bananaLimit_firstOrder_aleph0_categorical :
    Cardinal.Categorical Cardinal.aleph0 (bananaTaggedLanguage.completeTheory BananaTaggedCarrier) :=
  categorical_completeTheory_of_finite_tupleOrbitRepresentatives
    bananaLimit_firstOrder_finite_tuple_orbit_representatives

end SuccessorTree.NonPrecompact
