import BANANA.NonPrecompact.BananaSortedSyntax

/-!
# Interpreting tagged formulas in the two-sorted BANANA language

Fix the sorts of the free variables. A quantifier in the tagged language
ranges over the disjoint union, so it is split into one quantifier for each
sort. Separate auxiliary variables carry the two choices of sort for a
bound variable without capturing any free variable.
-/

namespace SuccessorTree.NonPrecompact.BananaSorted

open FirstOrder
open scoped FirstOrder

universe u v

variable {α : Type u} {sort : α → BananaSort}

local instance : DecidableEq BananaSort
  | .left, .left => isTrue rfl
  | .right, .right => isTrue rfl
  | .left, .right => isFalse (by nofun)
  | .right, .left => isFalse (by nofun)

private def Formula.neg (φ : Formula sort) : Formula sort := .imp φ .falsum

private def Formula.conj (φ ψ : Formula sort) : Formula sort :=
  (φ.imp ψ.neg).neg

private def Formula.all (i : α) (φ : Formula sort) : Formula sort :=
  (Formula.ex i φ.neg).neg

private def Formula.truth : Formula sort := (Formula.falsum : Formula sort).neg

/-- Use the variable as a term of the requested sort when this is well-typed. -/
private def withSort (s : BananaSort) (i : α) (f : Term sort s → Formula sort) :
    Formula sort :=
  if h : sort i = s then f (h ▸ Term.var i) else .falsum

private def fromAdd (s : BananaSort) (x y z : α) : Formula sort :=
  withSort s x fun a => withSort s y fun b => withSort s z fun c => .equal c (.add a b)

private def fromRel {n : ℕ} (r : bananaTaggedLanguage.Relations n) (i : Fin n → α) :
    Formula sort :=
  match r with
  | .left => withSort .left (i 0) fun _ => .truth
  | .right => withSort .right (i 0) fun _ => .truth
  | .leftZero => withSort .left (i 0) fun x => .equal x (.zero .left)
  | .rightZero => withSort .right (i 0) fun x => .equal x (.zero .right)
  | .leftAdd => fromAdd .left (i 0) (i 1) (i 2)
  | .rightAdd => fromAdd .right (i 0) (i 1) (i 2)
  | .edge => withSort .left (i 0) fun x => withSort .right (i 1) fun y => .edge x y

private def fromEq (i j : α) : Formula sort :=
  withSort (sort i) j fun t => .equal (.var i) t

section Relations

variable {V : BananaSort → Type v}

private theorem reverse_tag_injective (s : BananaSort) :
    Function.Injective (tag (V := V) (s := s)) := by
  cases s
  · exact Sum.inl_injective
  · exact Sum.inr_injective

private theorem sort_eq_of_tag_eq {s t : BananaSort} {x : V s} {y : V t}
    (h : tag x = tag y) : s = t := by
  cases s <;> cases t <;> simp [tag] at h ⊢

variable [∀ s, Zero (V s)] [∀ s, Add (V s)]
  [DecidableEq α] (pair : V .left → V .right → F2) (a : ∀ i, V (sort i))

private theorem realize_neg (φ : Formula sort) :
    φ.neg.realize pair a ↔ ¬ φ.realize pair a := Iff.rfl

private theorem realize_conj (φ ψ : Formula sort) :
    (φ.conj ψ).realize pair a ↔ φ.realize pair a ∧ ψ.realize pair a := by
  classical
  simp only [Formula.conj, realize_neg, Formula.realize, not_imp, not_not]

private theorem realize_all (i : α) (φ : Formula sort) :
    (φ.all i).realize pair a ↔ ∀ x, φ.realize pair (Function.update a i x) := by
  classical
  simp only [Formula.all, realize_neg, Formula.realize, not_exists, not_not]

private theorem realize_withSort (s : BananaSort) (i : α)
    (f : Term sort s → Formula sort) (p : V s → Prop)
    (hf : ∀ t, (f t).realize pair a ↔ p (t.realize a)) :
    (withSort s i f).realize pair a ↔ ∃ x : V s, tag (a i) = tag x ∧ p x := by
  by_cases h : sort i = s
  · subst s
    rw [withSort, dite_eq_left rfl, hf]
    change p (a i) ↔ _
    constructor
    · exact fun hp => ⟨a i, rfl, hp⟩
    · rintro ⟨x, hx, hp⟩
      have he := reverse_tag_injective (sort i) hx
      exact he.symm ▸ hp
  · rw [withSort, dite_eq_right h]
    change False ↔ _
    constructor
    · exact False.elim
    · exact fun ⟨_x, hx, _⟩ => h (sort_eq_of_tag_eq hx)

private theorem realize_fromEq (i j : α) :
    (fromEq i j).realize pair a ↔ tag (a i) = tag (a j) := by
  refine (realize_withSort pair a _ _ _ (fun x => a i = x) (fun _ => Iff.rfl)).trans ?_
  constructor
  · rintro ⟨x, hx, he⟩
    subst x
    exact hx.symm
  · exact fun h => ⟨a i, h.symm, rfl⟩

private theorem realize_fromAdd (s : BananaSort) (i j k : α) :
    (fromAdd s i j k).realize pair a ↔
      ∃ x y : V s, tag (a i) = tag x ∧ tag (a j) = tag y ∧ tag (a k) = tag (x + y) := by
  refine (realize_withSort pair a _ _ _
    (fun x => ∃ y : V s, tag (a j) = tag y ∧ tag (a k) = tag (x + y)) ?_).trans ?_
  · intro x
    refine realize_withSort pair a _ _ _ (fun y => tag (a k) = tag (x.realize a + y)) ?_
    intro y
    refine (realize_withSort pair a _ _ _
      (fun z => z = x.realize a + y.realize a) (fun _ => Iff.rfl)).trans ?_
    simp
  · constructor
    · rintro ⟨x, hi, y, hj, hk⟩
      exact ⟨x, y, hi, hj, hk⟩
    · rintro ⟨x, y, hi, hj, hk⟩
      exact ⟨x, hi, y, hj, hk⟩

private theorem realize_fromRel {n : ℕ} (r : bananaTaggedLanguage.Relations n) (i : Fin n → α) :
    letI := bananaTaggedPairingStructure pair
    (fromRel r i).realize pair a ↔
      Language.Structure.RelMap (L := bananaTaggedLanguage) r (fun j => tag (a (i j))) := by
  let _ := bananaTaggedPairingStructure pair
  cases r with
  | left =>
    change (withSort .left (i 0) (fun _ => .truth)).realize pair a ↔
      ∃ x : V .left, tag (a (i 0)) = tag x
    exact (realize_withSort pair a _ _ _ (fun _ => True) (fun _ => by
      simp [Formula.truth, Formula.neg, Formula.realize])).trans (by simp)
  | right =>
    change (withSort .right (i 0) (fun _ => .truth)).realize pair a ↔
      ∃ x : V .right, tag (a (i 0)) = tag x
    exact (realize_withSort pair a _ _ _ (fun _ => True) (fun _ => by
      simp [Formula.truth, Formula.neg, Formula.realize])).trans (by simp)
  | leftZero =>
    change (withSort .left (i 0) (fun x => .equal x (.zero .left))).realize pair a ↔
      tag (a (i 0)) = tag (V := V) (s := .left) 0
    exact (realize_withSort pair a _ _ _ (fun y => y = 0) (fun _ => Iff.rfl)).trans (by simp)
  | rightZero =>
    change (withSort .right (i 0) (fun x => .equal x (.zero .right))).realize pair a ↔
      tag (a (i 0)) = tag (V := V) (s := .right) 0
    exact (realize_withSort pair a _ _ _ (fun y => y = 0) (fun _ => Iff.rfl)).trans (by simp)
  | leftAdd => exact realize_fromAdd pair a .left (i 0) (i 1) (i 2)
  | rightAdd => exact realize_fromAdd pair a .right (i 0) (i 1) (i 2)
  | edge =>
    change (withSort .left (i 0) (fun x => withSort .right (i 1) (fun y => .edge x y))).realize pair a ↔
      ∃ x : V .left, ∃ y : V .right, tag (a (i 0)) = tag x ∧ tag (a (i 1)) = tag y ∧ pair x y = 1
    refine (realize_withSort pair a _ _ _
      (fun x => ∃ y : V .right, tag (a (i 1)) = tag y ∧ pair x y = 1) ?_).trans ?_
    · intro x
      exact realize_withSort pair a _ _ _ (fun y => pair (x.realize a) y = 1) (fun _ => Iff.rfl)
    · constructor
      · rintro ⟨x, hx, y, hy, h⟩
        exact ⟨x, y, hx, hy, h⟩
      · rintro ⟨x, y, hx, hy, h⟩
        exact ⟨x, hx, y, hy, h⟩

end Relations

/-- Auxiliary variables store one possible binding for each position and sort. -/
abbrev SyntaxVariable (α : Type u) := α ⊕ (ℕ × BananaSort)

/-- The variable stock extends the chosen sorts of the free variables. -/
def syntaxSort (sort : α → BananaSort) : SyntaxVariable α → BananaSort :=
  Sum.elim sort Prod.snd

private def variableOf {γ : Type*} : bananaTaggedLanguage.Term γ → γ
  | .var i => i
  | .func f _ => Empty.elim f

private theorem realize_variableOf {γ X : Type*} [bananaTaggedLanguage.Structure X]
    (a : γ → X) (t : bananaTaggedLanguage.Term γ) :
    t.realize a = a (variableOf t) := by
  cases t with
  | var => rfl
  | func f _ => exact Empty.elim f

private def contextVariable {n : ℕ} (s : Fin n → BananaSort) :
    α ⊕ Fin n → SyntaxVariable α :=
  Sum.elim Sum.inl (fun i => .inr (i.val, s i))

private def fromTaggedBounded {n : ℕ} :
    bananaTaggedLanguage.BoundedFormula α n → (Fin n → BananaSort) → Formula (syntaxSort sort)
  | .falsum, _ => .falsum
  | .equal t u, s => fromEq (contextVariable s (variableOf t)) (contextVariable s (variableOf u))
  | .rel r ts, s => fromRel r (fun i => contextVariable s (variableOf (ts i)))
  | .imp φ ψ, s => .imp (fromTaggedBounded φ s) (fromTaggedBounded ψ s)
  | @Language.BoundedFormula.all _ _ n φ, s =>
    (Formula.all (.inr (n, .left)) (fromTaggedBounded φ (Fin.snoc s .left))).conj
      (Formula.all (.inr (n, .right)) (fromTaggedBounded φ (Fin.snoc s .right)))

/-- Interpret a tagged formula as a two-sorted formula after assigning a
sort to each free variable. -/
def fromTagged (sort : α → BananaSort) (φ : bananaTaggedLanguage.Formula α) :
    Formula (syntaxSort sort) :=
  fromTaggedBounded φ Fin.elim0

section Realization

variable {V : BananaSort → Type v}

private def freeValues (a : ∀ i, V (syntaxSort sort i)) (i : α) : V .left ⊕ V .right :=
  tag (a (.inl i))

private def boundValues {n : ℕ} (a : ∀ i, V (syntaxSort sort i))
    (s : Fin n → BananaSort) (i : Fin n) : V .left ⊕ V .right :=
  tag (a (.inr (i.val, s i)))

private theorem contextValues {n : ℕ} (a : ∀ i, V (syntaxSort sort i)) (s : Fin n → BananaSort) :
    Sum.elim (freeValues a) (boundValues a s) = fun i => tag (a (contextVariable s i)) := by
  funext i
  cases i <;> rfl

variable [DecidableEq α]

private theorem freeValues_update {n : ℕ} {s : BananaSort}
    (a : ∀ i, V (syntaxSort sort i)) (x : V s) :
    freeValues (Function.update a (.inr (n,s)) x) = freeValues a := by
  funext i
  have hne : (Sum.inl i : SyntaxVariable α) ≠ Sum.inr (n,s) := Sum.inl_ne_inr
  exact congrArg (tag (V := V) (s := sort i))
    (Function.update_of_ne (β := fun i => V (syntaxSort sort i)) hne x a)

private theorem boundValues_update {n : ℕ} {s : BananaSort}
    (a : ∀ i, V (syntaxSort sort i)) (bs : Fin n → BananaSort) (x : V s) :
    boundValues (Function.update a (.inr (n,s)) x) (Fin.snoc bs s) =
      Fin.snoc (boundValues a bs) (tag x) := by
  let extended : Fin (n + 1) → BananaSort := Fin.snoc bs s
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hidx : (Sum.inr ((Fin.last n).val, extended (Fin.last n)) : SyntaxVariable α) =
        Sum.inr (n,s) := by simp [extended]
    refine (congrArg (fun j : SyntaxVariable α => tag (V := V)
      (Function.update a (.inr (n,s)) x j)) hidx).trans ?_
    simp only [Fin.snoc_last]
    exact congrArg (tag (V := V) (s := s))
      (Function.update_self (β := fun i => V (syntaxSort sort i)) (.inr (n,s)) x a)
  · have hidx : (Sum.inr (j.castSucc.val, extended j.castSucc) : SyntaxVariable α) =
        Sum.inr (j.val, bs j) := by simp [extended]
    refine (congrArg (fun q : SyntaxVariable α => tag (V := V)
      (Function.update a (.inr (n,s)) x q)) hidx).trans ?_
    simp only [Fin.snoc_castSucc]
    have hne : (Sum.inr (j.val, bs j) : SyntaxVariable α) ≠ Sum.inr (n,s) :=
      fun h => (Nat.ne_of_lt j.isLt) (congrArg Prod.fst (Sum.inr_injective h))
    exact congrArg (tag (V := V) (s := bs j))
      (Function.update_of_ne (β := fun i => V (syntaxSort sort i)) hne x a)

variable [∀ s, Zero (V s)] [∀ s, Add (V s)]
  (pair : V .left → V .right → F2)

private theorem realize_fromTaggedBounded {n : ℕ} (φ : bananaTaggedLanguage.BoundedFormula α n)
    (s : Fin n → BananaSort) (a : ∀ i, V (syntaxSort sort i)) :
    letI := bananaTaggedPairingStructure pair
    (fromTaggedBounded φ s).realize pair a ↔ φ.Realize (freeValues a) (boundValues a s) := by
  let _ := bananaTaggedPairingStructure pair
  induction φ generalizing a with
  | falsum => rfl
  | equal t u =>
    change (fromEq (contextVariable s (variableOf t)) (contextVariable s (variableOf u))).realize pair a ↔
      t.realize (Sum.elim _ _) = u.realize (Sum.elim _ _)
    rw [realize_fromEq, realize_variableOf, realize_variableOf, contextValues]
  | rel r ts =>
    change (fromRel r (fun i => contextVariable s (variableOf (ts i)))).realize pair a ↔
      Language.Structure.RelMap (L := bananaTaggedLanguage) r
        (fun i => (ts i).realize (Sum.elim _ _))
    rw [realize_fromRel]
    simp only [realize_variableOf, contextValues]
  | imp φ ψ hf hg =>
    simp only [fromTaggedBounded, Formula.realize, Language.BoundedFormula.realize_imp, hf, hg]
  | @all n φ ih =>
    change
      ((Formula.all (.inr (n, .left)) (fromTaggedBounded φ (Fin.snoc s .left))).conj
        (Formula.all (.inr (n, .right)) (fromTaggedBounded φ (Fin.snoc s .right)))).realize pair a ↔
        ∀ x, φ.Realize (freeValues a) (Fin.snoc (boundValues a s) x)
    simp only [realize_conj, realize_all, ih]
    have bind (t : BananaSort) (x : V t) :
        φ.Realize (freeValues (Function.update a (.inr (n,t)) x))
          (boundValues (Function.update a (.inr (n,t)) x) (Fin.snoc s t)) ↔
          φ.Realize (freeValues a) (Fin.snoc (boundValues a s) (tag (V := V) x)) := by
      rw [freeValues_update (V := V) (s := t) a x, boundValues_update (V := V) (s := t) a s x]
    constructor
    · rintro ⟨hl, hr⟩ (x | y)
      · exact (bind .left x).mp (hl x)
      · exact (bind .right y).mp (hr y)
    · exact fun h => ⟨fun x => (bind .left x).mpr (h (.inl x)),
        fun y => (bind .right y).mpr (h (.inr y))⟩

/-- For a sorted assignment the reverse translation preserves truth,
independently of the initial values of the extra variables. -/
theorem realize_fromTagged (φ : bananaTaggedLanguage.Formula α)
    (a : ∀ i, V (syntaxSort sort i)) :
    letI := bananaTaggedPairingStructure pair
    (fromTagged sort φ).realize pair a ↔ φ.Realize (fun i => tag (a (.inl i))) := by
  let _ := bananaTaggedPairingStructure pair
  have h := realize_fromTaggedBounded pair φ Fin.elim0 a
  rwa [show boundValues a (Fin.elim0 : Fin 0 → BananaSort) =
    (default : Fin 0 → V .left ⊕ V .right) from Subsingleton.elim _ _] at h

/-- Extend a sorted tuple by assigning zero to every auxiliary variable. -/
def zeroExtend (a : ∀ i, V (sort i)) : ∀ i, V (syntaxSort sort i)
  | .inl i => a i
  | .inr _ => 0

private def zeroBinder (s : BananaSort) : Fin 2 :=
  match s with
  | .left => 0
  | .right => 1

private def collapseAux : SyntaxVariable α → α ⊕ Fin 2 :=
  Sum.map id (zeroBinder ∘ Prod.snd)

private def leftZeroWitness : bananaTaggedLanguage.Formula (α ⊕ Fin 2) :=
  Language.Relations.formula₁ (L := bananaTaggedLanguage) .leftZero (.var (.inr 0))

private def rightZeroWitness : bananaTaggedLanguage.Formula (α ⊕ Fin 2) :=
  Language.Relations.formula₁ (L := bananaTaggedLanguage) .rightZero (.var (.inr 1))

private noncomputable def translateWithZeros (φ : Formula (syntaxSort sort)) :
    bananaTaggedLanguage.Formula α :=
  ((φ.translate.relabel collapseAux ⊓ leftZeroWitness) ⊓ rightZeroWitness).iExs (Fin 2)

private theorem realize_translateWithZeros (φ : Formula (syntaxSort sort)) (a : ∀ i, V (sort i)) :
    letI := bananaTaggedPairingStructure pair
    (translateWithZeros φ).Realize (fun i => tag (a i)) ↔ φ.realize pair (zeroExtend a) := by
  let _ := bananaTaggedPairingStructure pair
  let v (i : α) := tag (a i)
  let z : Fin 2 → V .left ⊕ V .right := ![Sum.inl 0, Sum.inr 0]
  have left (w : Fin 2 → V .left ⊕ V .right) :
      (leftZeroWitness (α := α)).Realize (Sum.elim v w) ↔ w 0 = z 0 :=
    Language.Formula.realize_rel₁ (L := bananaTaggedLanguage)
  have right (w : Fin 2 → V .left ⊕ V .right) :
      (rightZeroWitness (α := α)).Realize (Sum.elim v w) ↔ w 1 = z 1 :=
    Language.Formula.realize_rel₁ (L := bananaTaggedLanguage)
  have val : Sum.elim v z ∘ collapseAux = fun i => tag (zeroExtend a i) := by
    funext i
    rcases i with i | ⟨n,s⟩
    · rfl
    · cases s <;> rfl
  change (translateWithZeros φ).Realize v ↔ _
  simp only [translateWithZeros, Language.Formula.realize_iExs, Language.Formula.realize_inf,
    Language.Formula.realize_relabel, left, right]
  constructor
  · rintro ⟨w, ⟨h, hleft⟩, hright⟩
    have hval : w = z := by
      funext i
      fin_cases i
      · exact hleft
      · exact hright
    rw [hval, val] at h
    exact (φ.realize_translate pair (zeroExtend a)).mp h
  · intro h
    refine ⟨z, ⟨?_, rfl⟩, rfl⟩
    rw [val]
    exact (φ.realize_translate pair (zeroExtend a)).mpr h

variable {n : ℕ} {indices : Fin n → BananaSort}

/-- Tagged finite tuples have the same complete type precisely when their
sorted versions agree on all two-sorted formulas. Auxiliary variables have
fixed value zero, so they do not introduce any free parameters. -/
theorem sameFormulaType_iff_sorted (a b : ∀ i, V (indices i)) :
    letI := bananaTaggedPairingStructure pair
    SameFormulaType (L := bananaTaggedLanguage) (fun i => tag (a i)) (fun i => tag (b i)) ↔
      ∀ φ : Formula (syntaxSort indices),
        φ.realize pair (zeroExtend a) ↔ φ.realize pair (zeroExtend b) := by
  let _ := bananaTaggedPairingStructure pair
  constructor
  · intro h φ
    exact (realize_translateWithZeros pair φ a).symm.trans
      ((h (translateWithZeros φ)).trans (realize_translateWithZeros pair φ b))
  · intro h φ
    exact (realize_fromTagged pair φ (zeroExtend a)).symm.trans
      ((h (fromTagged indices φ)).trans (realize_fromTagged pair φ (zeroExtend b)))

end Realization

section Decoded

variable (M : Type v) [bananaTaggedLanguage.Structure M]
  [M ⊨ bananaTaggedLanguage.completeTheory BananaTaggedCarrier] [DecidableEq α]

/-- In a model of the complete tagged BANANA theory, its decoded sorted
structure interprets every tagged formula under the corresponding assignment. -/
theorem realize_fromTagged_decoded (φ : bananaTaggedLanguage.Formula α)
    (a : ∀ i, (syntaxSort sort i).Carrier M) :
    (fromTagged sort φ).realize (V := fun s => s.Carrier M)
      (fun x y => bananaTaggedModelPairing (M := M) x y) a ↔
      φ.Realize (fun i => (a (.inl i)).val) := by
  let pair (x : BananaSort.left.Carrier M) (y : BananaSort.right.Carrier M) :=
    bananaTaggedModelPairing (M := M) x y
  let _ := bananaTaggedPairingStructure pair
  let e := bananaTaggedModelPairingEquiv (M := M)
  have h (s : BananaSort) (x : s.Carrier M) :
      e (tag (V := fun s => s.Carrier M) x) = x.val := by
    cases s <;> rfl
  have he := Language.StrongHomClass.realize_formula e φ
    (v := fun i => tag (V := fun s => s.Carrier M) (a (.inl i)))
  rw [show e ∘ (fun i => tag (V := fun s => s.Carrier M) (a (.inl i))) =
    (fun i => (a (.inl i)).val) from funext fun i => h _ (a (.inl i))] at he
  exact (realize_fromTagged (V := fun s => s.Carrier M) pair φ a).trans he.symm

end Decoded

end SuccessorTree.NonPrecompact.BananaSorted
