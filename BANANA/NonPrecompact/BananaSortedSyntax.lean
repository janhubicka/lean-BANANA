import BANANA.NonPrecompact.BananaTaggedModelDecoding

/-!
# The two-sorted BANANA language

Terms are sorted variables, zero, and addition. Atomic formulas are
same-sort equality and the edge relation. The translation into the
tagged relational language uses existential witnesses for term values
and restricts each quantifier to its designated sort.
-/

namespace SuccessorTree.NonPrecompact.BananaSorted

open FirstOrder
open scoped FirstOrder

universe u v

variable {α : Type u} {sort : α → BananaSort}

/-- Terms in either of the two additive sorts. -/
inductive Term (sort : α → BananaSort) : BananaSort → Type u
  | var (i : α) : Term sort (sort i)
  | zero (s : BananaSort) : Term sort s
  | add {s : BananaSort} : Term sort s → Term sort s → Term sort s

/-- Formulas over a stock of named variables with fixed sorts.
Existential quantification replaces the assignment of the indicated variable. -/
inductive Formula (sort : α → BananaSort) : Type u
  | falsum : Formula sort
  | equal {s : BananaSort} : Term sort s → Term sort s → Formula sort
  | edge : Term sort .left → Term sort .right → Formula sort
  | imp : Formula sort → Formula sort → Formula sort
  | ex (i : α) : Formula sort → Formula sort

section Interpret

variable {V : BananaSort → Type v} [∀ s, Zero (V s)] [∀ s, Add (V s)]

/-- The value of a term lies in its syntactically specified sort. -/
def Term.realize (a : ∀ i, V (sort i)) {s : BananaSort} : Term sort s → V s
  | .var i => a i
  | .zero _ => 0
  | .add t u => t.realize a + u.realize a

variable [DecidableEq α]

/-- Satisfaction using ordinary sorted variable assignments. -/
def Formula.realize (pair : V .left → V .right → F2)
    (a : ∀ i, V (sort i)) : Formula sort → Prop
  | .falsum => False
  | .equal t u => t.realize a = u.realize a
  | .edge t u => pair (t.realize a) (u.realize a) = 1
  | .imp φ ψ => φ.realize pair a → ψ.realize pair a
  | .ex i φ => ∃ x : V (sort i), φ.realize pair (Function.update a i x)

end Interpret

private abbrev TaggedFormula (α : Type*) := bananaTaggedLanguage.Formula α

private def sortRel : BananaSort → bananaTaggedLanguage.Relations 1
  | .left => .left
  | .right => .right

private def zeroRel : BananaSort → bananaTaggedLanguage.Relations 1
  | .left => .leftZero
  | .right => .rightZero

private def addRel : BananaSort → bananaTaggedLanguage.Relations 3
  | .left => .leftAdd
  | .right => .rightAdd

private def sortAtom (s : BananaSort) (i : α) : TaggedFormula α :=
  Language.Relations.formula₁ (L := bananaTaggedLanguage) (sortRel s) (.var i)

private def zeroAtom (s : BananaSort) (i : α) : TaggedFormula α :=
  Language.Relations.formula₁ (L := bananaTaggedLanguage) (zeroRel s) (.var i)

private def addAtom (s : BananaSort) (i j k : α) : TaggedFormula α :=
  Language.Relations.formula (L := bananaTaggedLanguage) (addRel s) ![.var i, .var j, .var k]

private def edgeAtom (i j : α) : TaggedFormula α :=
  Language.Relations.formula₂ (L := bananaTaggedLanguage) .edge (.var i) (.var j)

/-- Supply two term values to an atomic formula by quantifying their witnesses. -/
private noncomputable def withTermPair {β : Type*} (ι : α → β)
    (first second : TaggedFormula (α ⊕ Unit)) (body : TaggedFormula (β ⊕ Fin 2)) :
    TaggedFormula β :=
  let witness (i : Fin 2) : α ⊕ Unit → β ⊕ Fin 2 :=
    Sum.elim (Sum.inl ∘ ι) (fun _ => .inr i)
  ((first.relabel (witness 0) ⊓ second.relabel (witness 1)) ⊓ body).iExs (Fin 2)

/-- In the graph formula the variable `Sum.inr ()` represents the term's value. -/
noncomputable def Term.graph {s : BananaSort} (t : Term sort s) :
    bananaTaggedLanguage.Formula (α ⊕ Unit) :=
  match t with
  | .var i => (.var (.inr ()) : bananaTaggedLanguage.Term _).equal (.var (.inl i))
  | .zero s => zeroAtom s (.inr ())
  | .add t u => withTermPair Sum.inl t.graph u.graph
      (addAtom s (.inr 0) (.inr 1) (.inl (.inr ())))

private def bindVar [DecidableEq α] (i j : α) : α ⊕ Unit :=
  if j = i then .inr () else .inl j

/-- Translate the two-sorted formula into the tagged one-sorted language. -/
noncomputable def Formula.translate [DecidableEq α] : Formula sort → bananaTaggedLanguage.Formula α
  | .falsum => ⊥
  | .equal t u => withTermPair id t.graph u.graph
      ((.var (.inr 0) : bananaTaggedLanguage.Term _).equal (.var (.inr 1)))
  | .edge t u => withTermPair id t.graph u.graph (edgeAtom (.inr 0) (.inr 1))
  | .imp φ ψ => φ.translate.imp ψ.translate
  | .ex i φ => (sortAtom (sort i) (.inr ()) ⊓ φ.translate.relabel (bindVar i)).iExs Unit

section TaggedInterpret

variable {V : BananaSort → Type v}

/-- Include a vector into the tagged sum using its sort. -/
def tag {s : BananaSort} (x : V s) : V .left ⊕ V .right :=
  match s, x with
  | .left, x => .inl x
  | .right, x => .inr x

private theorem tag_injective (s : BananaSort) :
    Function.Injective (tag (V := V) (s := s)) := by
  cases s
  · exact Sum.inl_injective
  · exact Sum.inr_injective

variable [DecidableEq α] in
private theorem tag_update (a : ∀ i, V (sort i)) (i : α) (x : V (sort i)) :
    Sum.elim (fun j => tag (a j)) (fun _ => tag x) ∘ bindVar i =
      fun j => tag (Function.update a i x j) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [bindVar]
  · simp [bindVar, h]

variable [∀ s, Zero (V s)] [∀ s, Add (V s)]
variable (pair : V .left → V .right → F2)

private theorem realize_sortAtom (s : BananaSort) (i : α) (a : α → V .left ⊕ V .right) :
    letI := bananaTaggedPairingStructure pair
    (sortAtom s i).Realize a ↔ ∃ x : V s, a i = tag x := by
  let _ := bananaTaggedPairingStructure pair
  cases s <;> exact Language.Formula.realize_rel₁ (L := bananaTaggedLanguage)

private theorem realize_zeroAtom (s : BananaSort) (i : α) (a : α → V .left ⊕ V .right) :
    letI := bananaTaggedPairingStructure pair
    (zeroAtom s i).Realize a ↔ a i = (tag (V := V) (s := s) 0) := by
  let _ := bananaTaggedPairingStructure pair
  cases s <;> exact Language.Formula.realize_rel₁ (L := bananaTaggedLanguage)

private theorem realize_addAtom (s : BananaSort) (i j k : α) (a : α → V .left ⊕ V .right)
    (x y : V s) (hx : a i = tag x) (hy : a j = tag y) :
    letI := bananaTaggedPairingStructure pair
    (addAtom s i j k).Realize a ↔ a k = tag (x + y) := by
  let _ := bananaTaggedPairingStructure pair
  rw [addAtom, Language.Formula.realize_rel (R := addRel s)]
  have h : (fun n => ( (![.var i, .var j, .var k] :
      Fin 3 → bananaTaggedLanguage.Term α) n).realize a) = ![a i, a j, a k] := by
    funext n
    fin_cases n <;> rfl
  rw [h, hx, hy]
  cases s with
  | left =>
    change (∃ b c : V .left, Sum.inl x = Sum.inl b ∧ Sum.inl y = Sum.inl c ∧
      a k = Sum.inl (b + c)) ↔ a k = Sum.inl (x + y)
    simp
  | right =>
    change (∃ b c : V .right, Sum.inr x = Sum.inr b ∧ Sum.inr y = Sum.inr c ∧
      a k = Sum.inr (b + c)) ↔ a k = Sum.inr (x + y)
    simp

private theorem realize_edgeAtom (i j : α) (a : α → V .left ⊕ V .right)
    (x : V .left) (y : V .right) (hx : a i = tag x) (hy : a j = tag y) :
    letI := bananaTaggedPairingStructure pair
    (edgeAtom i j).Realize a ↔ pair x y = 1 := by
  let _ := bananaTaggedPairingStructure pair
  rw [edgeAtom, Language.Formula.realize_rel₂ (L := bananaTaggedLanguage) (R := .edge),
    Language.Term.realize_var,
    Language.Term.realize_var, hx, hy]
  change (∃ b c, Sum.inl x = Sum.inl b ∧ Sum.inr y = Sum.inr c ∧ pair b c = 1) ↔ pair x y = 1
  simp

variable {M : Type v} [bananaTaggedLanguage.Structure M]

private theorem realize_withTermPair {β : Type*} (ι : α → β) (a : β → M)
    (first second : TaggedFormula (α ⊕ Unit)) (body : TaggedFormula (β ⊕ Fin 2))
    (x y : M)
    (hx : ∀ z, first.Realize (Sum.elim (a ∘ ι) (fun _ => z)) ↔ z = x)
    (hy : ∀ z, second.Realize (Sum.elim (a ∘ ι) (fun _ => z)) ↔ z = y) :
    (withTermPair ι first second body).Realize a ↔ body.Realize (Sum.elim a ![x, y]) := by
  simp only [withTermPair, Language.Formula.realize_iExs, Language.Formula.realize_inf,
    Language.Formula.realize_relabel]
  have h (w : Fin 2 → M) (i : Fin 2) :
      Sum.elim a w ∘ (Sum.elim (Sum.inl ∘ ι) (fun _ : Unit => Sum.inr i)) =
        Sum.elim (a ∘ ι) (fun _ : Unit => w i) := by
    funext j
    cases j <;> rfl
  constructor
  · rintro ⟨w, ⟨hw₀, hw₁⟩, hb⟩
    rw [h] at hw₀ hw₁
    have heq : w = ![x, y] := by
      funext i
      fin_cases i
      · exact (hx (w 0)).mp hw₀
      · exact (hy (w 1)).mp hw₁
    rwa [heq] at hb
  · intro hb
    refine ⟨![x, y], ⟨?_, ?_⟩, hb⟩
    · rw [h, hx]
      rfl
    · rw [h, hy]
      rfl

/-- The graph formula defines exactly the tagged value of a term. -/
theorem Term.realize_graph {s : BananaSort} (t : Term sort s) (a : ∀ i, V (sort i))
    (z : V .left ⊕ V .right) :
    letI := bananaTaggedPairingStructure pair
    t.graph.Realize (Sum.elim (fun i => tag (a i)) (fun _ => z)) ↔ z = tag (t.realize a) := by
  let _ := bananaTaggedPairingStructure pair
  induction t generalizing z with
  | var i =>
    simp [Term.graph, Term.realize]
  | zero s =>
    exact realize_zeroAtom pair s (Sum.inr () : α ⊕ Unit) _
  | @add s t u ih₁ ih₂ =>
    rw [Term.graph, realize_withTermPair (x := tag (t.realize a)) (y := tag (u.realize a))]
    · exact realize_addAtom pair s (Sum.inr 0 : (α ⊕ Unit) ⊕ Fin 2)
        (Sum.inr 1) (Sum.inl (Sum.inr ())) _
        (t.realize a) (u.realize a) rfl rfl
    · exact ih₁
    · exact ih₂

variable [DecidableEq α]

/-- Translation preserves the truth of every two-sorted formula under every
sorted assignment, for any two additive sorts and pairing. -/
theorem Formula.realize_translate (φ : Formula sort) (a : ∀ i, V (sort i)) :
    letI := bananaTaggedPairingStructure pair
    φ.translate.Realize (fun i => tag (a i)) ↔ φ.realize pair a := by
  let _ := bananaTaggedPairingStructure pair
  induction φ generalizing a with
  | falsum =>
    rfl
  | @equal s t u =>
    rw [Formula.translate, realize_withTermPair (x := tag (t.realize a)) (y := tag (u.realize a))]
    · simpa only [Language.Formula.realize_equal, Language.Term.realize_var,
        Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Formula.realize] using
        (tag_injective (V := V) s).eq_iff
    · exact t.realize_graph pair a
    · exact u.realize_graph pair a
  | edge t u =>
    rw [Formula.translate, realize_withTermPair (x := tag (t.realize a)) (y := tag (u.realize a))]
    · exact realize_edgeAtom pair (Sum.inr 0 : α ⊕ Fin 2) (Sum.inr 1) _
        (t.realize a) (u.realize a) rfl rfl
    · exact t.realize_graph pair a
    · exact u.realize_graph pair a
  | imp φ ψ ihφ ihψ =>
    simp only [Formula.translate, Language.Formula.realize_imp, Formula.realize, ihφ, ihψ]
  | ex i φ ih =>
    simp only [Formula.translate, Language.Formula.realize_iExs, Language.Formula.realize_inf,
      Language.Formula.realize_relabel, Formula.realize]
    constructor
    · rintro ⟨w, hs, hφ⟩
      obtain ⟨x, hx⟩ := (realize_sortAtom pair (sort i) (Sum.inr () : α ⊕ Unit) _).mp hs
      have hw : w = fun _ => tag x := funext fun u => by cases u; exact hx
      subst w
      rw [tag_update] at hφ
      exact ⟨x, (ih _).mp hφ⟩
    · rintro ⟨x, hx⟩
      refine ⟨fun _ => tag x,
        (realize_sortAtom pair (sort i) (Sum.inr () : α ⊕ Unit) _).mpr ⟨x, rfl⟩, ?_⟩
      rw [tag_update]
      exact (ih _).mpr hx

end TaggedInterpret

variable [DecidableEq α] in
/-- The translation also uses the original tagged presentation of the
concrete BANANA limit. -/
theorem Formula.realize_translate_limit (φ : Formula sort) (a : α → BananaLimitVector) :
    φ.translate.Realize
      (fun i => tag (V := fun _ => BananaLimitVector) (s := sort i) (a i)) ↔
    φ.realize (V := fun _ => BananaLimitVector) bananaLimitPairing a := by
  let encoded := bananaTaggedPairingStructure bananaLimitPairing
  have h := @Language.StrongHomClass.realize_formula bananaTaggedLanguage
    BananaTaggedCarrier BananaTaggedCarrier encoded bananaTaggedStructure α _ _ _
    bananaTaggedNativePairingEquiv φ.translate
    (fun i => tag (V := fun _ => BananaLimitVector) (s := sort i) (a i))
  exact h.trans (φ.realize_translate (V := fun _ => BananaLimitVector) bananaLimitPairing a)

section Decoded

variable (M : Type v) [bananaTaggedLanguage.Structure M]
  [M ⊨ bananaTaggedLanguage.completeTheory BananaTaggedCarrier] [DecidableEq α]

/-- The same translation holds in every tagged BANANA model when sorted
assignments and the pairing are taken from its decoded vector sorts. -/
theorem Formula.realize_translate_decoded (φ : Formula sort)
    (a : ∀ i, (sort i).Carrier M) :
    φ.translate.Realize (fun i => (a i).val) ↔
      φ.realize (V := fun s => s.Carrier M)
        (fun x y => bananaTaggedModelPairing (M := M) x y) a := by
  let pair (x : BananaSort.left.Carrier M) (y : BananaSort.right.Carrier M) :=
    bananaTaggedModelPairing (M := M) x y
  let _ := bananaTaggedPairingStructure pair
  let e := bananaTaggedModelPairingEquiv (M := M)
  have h (s : BananaSort) (x : s.Carrier M) :
      e (tag (V := fun s => s.Carrier M) x) = x.val := by
    cases s <;> rfl
  have he := Language.StrongHomClass.realize_formula e φ.translate
    (v := fun i => tag (V := fun s => s.Carrier M) (a i))
  rw [show e ∘ (fun i => tag (V := fun s => s.Carrier M) (a i)) =
    (fun i => (a i).val) from funext fun i => h _ (a i)] at he
  exact he.trans (φ.realize_translate (V := fun s => s.Carrier M) pair a)

end Decoded

end SuccessorTree.NonPrecompact.BananaSorted
