import Mathlib.Algebra.Group.Hom.Basic

/-! # Unindexed coherent groupoid transport along a fixed class map
This is an abstract, source-independent test of the dependent quotient
bookkeeping in the BANANA coherent-EPPA statement. -/

namespace SuccessorTree.NonPrecompact

universe u v w t

variable {O : Type u} {I : Type v} {G : Type w}
variable {H : O → O → Type t}

abbrev GroupoidClassObject (cl : O → I) (c : I) :=
  {U : O // cl U = c}

/-- An indexed action is unchanged when a class equality is transported. -/
theorem classAction_changeIndex
    (cl : O → I)
    (Θ : ∀ (c : I) (U V : GroupoidClassObject cl c), H U.1 V.1 → G)
    {c d : I} (h : c = d) {U V : O}
    (hU : cl U = c) (hV : cl V = c) (p : H U V) :
    Θ c ⟨U, hU⟩ ⟨V, hV⟩ p =
      Θ d ⟨U, hU.trans h⟩ ⟨V, hV.trans h⟩ p := by
  cases h
  rfl

/-- The object class of the domain determines the action on each arrow. -/
def classAction_descend
    (cl : O → I)
    (same : ∀ {U V : O}, H U V → cl U = cl V)
    (Θ : ∀ (c : I) (U V : GroupoidClassObject cl c), H U.1 V.1 → G)
    {U V : O} (p : H U V) : G :=
  Θ (cl U) ⟨U, rfl⟩ ⟨V, (same p).symm⟩ p

/-- Identity coherence survives removal of the class index. -/
theorem classAction_descend_refl [Group G]
    (cl : O → I)
    (same : ∀ {U V : O}, H U V → cl U = cl V)
    (Θ : ∀ (c : I) (U V : GroupoidClassObject cl c), H U.1 V.1 → G)
    (reflH : ∀ (U : O), H U U)
    (hId : ∀ (c : I) (U : GroupoidClassObject cl c),
      Θ c U U (reflH U.1) = 1) (U : O) :
    classAction_descend cl same Θ (reflH U) = 1 := by
  exact hId (cl U) ⟨U, rfl⟩

/-- Composition coherence survives removal of the class index. -/
theorem classAction_descend_trans [Group G]
    (cl : O → I)
    (same : ∀ {U V : O}, H U V → cl U = cl V)
    (Θ : ∀ (c : I) (U V : GroupoidClassObject cl c), H U.1 V.1 → G)
    (transH : ∀ {U V W : O}, H U V → H V W → H U W)
    (hComp : ∀ (c : I) (U V W : GroupoidClassObject cl c)
        (p : H U.1 V.1) (q : H V.1 W.1),
        Θ c V W q * Θ c U V p = Θ c U W (transH p q))
    {U V W : O} (p : H U V) (q : H V W) :
    classAction_descend cl same Θ q * classAction_descend cl same Θ p =
      classAction_descend cl same Θ (transH p q) := by
  let c := cl U
  let u0 : GroupoidClassObject cl c := ⟨U, rfl⟩
  let v0 : GroupoidClassObject cl c := ⟨V, (same p).symm⟩
  let w0 : GroupoidClassObject cl c := ⟨W, (same (transH p q)).symm⟩
  have hq : classAction_descend cl same Θ q = Θ c v0 w0 q := by
    have he := classAction_changeIndex cl Θ (same p).symm
      (U := V) (V := W) rfl (same q).symm q
    exact he
  rw [hq]
  exact hComp c u0 v0 w0 p q

/-- Inversion coherence survives removal of the class index. -/
theorem classAction_descend_symm [Group G]
    (cl : O → I)
    (same : ∀ {U V : O}, H U V → cl U = cl V)
    (Θ : ∀ (c : I) (U V : GroupoidClassObject cl c), H U.1 V.1 → G)
    (symmH : ∀ {U V : O}, H U V → H V U)
    (hInv : ∀ (c : I) (U V : GroupoidClassObject cl c)
      (p : H U.1 V.1),
      (Θ c U V p)⁻¹ = Θ c V U (symmH p))
    {U V : O} (p : H U V) :
    (classAction_descend cl same Θ p)⁻¹ =
      classAction_descend cl same Θ (symmH p) := by
  let c := cl U
  let u0 : GroupoidClassObject cl c := ⟨U, rfl⟩
  let v0 : GroupoidClassObject cl c := ⟨V, (same p).symm⟩
  have hback : classAction_descend cl same Θ (symmH p) =
      Θ c v0 u0 (symmH p) := by
    have he := classAction_changeIndex cl Θ (same p).symm
      (U := V) (V := U) rfl (same p) (symmH p)
    exact he
  rw [hback]
  exact hInv c u0 v0 p

/-- A restriction property survives the class-index descent. -/
theorem classAction_descend_extends
    (cl : O → I)
    (same : ∀ {U V : O}, H U V → cl U = cl V)
    (Θ : ∀ (c : I) (U V : GroupoidClassObject cl c), H U.1 V.1 → G)
    (P : ∀ {U V : O}, H U V → G → Prop)
    (hExt : ∀ (c : I) (U V : GroupoidClassObject cl c)
      (p : H U.1 V.1), P p (Θ c U V p))
    {U V : O} (p : H U V) :
    P p (classAction_descend cl same Θ p) := by
  exact hExt (cl U) ⟨U, rfl⟩ ⟨V, (same p).symm⟩ p

end SuccessorTree.NonPrecompact
