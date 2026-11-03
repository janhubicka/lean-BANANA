import BANANA.NonPrecompact.FolkmanNonunitalTermNormalisation

/-!
# Genuine non-unital ring isomorphisms from finite tuple profiles

The generic construction uses equal ring-term equation kernels and
works in arbitrary Boolean rings. It explicitly preserves addition
and multiplication on native NonUnitalSubring carriers. The finite
Folkman signature theorem then supplies its kernel hypothesis.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

noncomputable def folkmanGeneratedRingTermRepresentative
    {n : ℕ} {α : Type*} [BooleanRing α]
    (xs : Fin n → α) (x : folkmanGeneratedNonunitalSubring xs) :
    FolkmanRingTerm n :=
  Classical.choose
    ((folkmanGeneratedNonunitalSubring_mem_iff_ringTerm xs x.val).mp x.property)

theorem folkmanGeneratedRingTermRepresentative_spec
    {n : ℕ} {α : Type*} [BooleanRing α]
    (xs : Fin n → α) (x : folkmanGeneratedNonunitalSubring xs) :
    (folkmanGeneratedRingTermRepresentative xs x).eval xs = x.val :=
  Classical.choose_spec
    ((folkmanGeneratedNonunitalSubring_mem_iff_ringTerm xs x.val).mp x.property)

noncomputable def folkmanGeneratedRingTermMap
    {n : ℕ} {α β : Type*} [BooleanRing α] [BooleanRing β]
    (xs : Fin n → α) (ys : Fin n → β)
    (x : folkmanGeneratedNonunitalSubring xs) :
    folkmanGeneratedNonunitalSubring ys :=
  ⟨(folkmanGeneratedRingTermRepresentative xs x).eval ys,
    (folkmanGeneratedRingTermRepresentative xs x).eval_mem_generated ys⟩

/-- Any representative gives the same target value when term equations transfer. -/
theorem folkmanGeneratedRingTermMap_eval
    {n : ℕ} {α β : Type*} [BooleanRing α] [BooleanRing β]
    (xs : Fin n → α) (ys : Fin n → β)
    (hEq : ∀ t u : FolkmanRingTerm n,
      t.eval xs = u.eval xs ↔ t.eval ys = u.eval ys)
    (x : folkmanGeneratedNonunitalSubring xs)
    (t : FolkmanRingTerm n) (ht : t.eval xs = x.val) :
    (folkmanGeneratedRingTermMap xs ys x).val = t.eval ys :=
  (hEq _ t).mp ((folkmanGeneratedRingTermRepresentative_spec xs x).trans ht.symm)

/-- Equal term-equation kernels give an actual ring isomorphism of the
native generated non-unital subrings, not just a carrier equivalence. -/
noncomputable def folkmanGeneratedNonunitalRingEquiv_of_termEqualities
    {n : ℕ} {α β : Type*} [BooleanRing α] [BooleanRing β]
    (xs : Fin n → α) (ys : Fin n → β)
    (hEq : ∀ t u : FolkmanRingTerm n,
      t.eval xs = u.eval xs ↔ t.eval ys = u.eval ys) :
    folkmanGeneratedNonunitalSubring xs ≃+*
      folkmanGeneratedNonunitalSubring ys where
  toFun := folkmanGeneratedRingTermMap xs ys
  invFun := folkmanGeneratedRingTermMap ys xs
  left_inv x := by
    apply Subtype.ext
    have h := folkmanGeneratedRingTermMap_eval ys xs
      (fun t u => (hEq t u).symm)
      (folkmanGeneratedRingTermMap xs ys x)
      (folkmanGeneratedRingTermRepresentative xs x) rfl
    exact h.trans (folkmanGeneratedRingTermRepresentative_spec xs x)
  right_inv y := by
    apply Subtype.ext
    have h := folkmanGeneratedRingTermMap_eval xs ys hEq
      (folkmanGeneratedRingTermMap ys xs y)
      (folkmanGeneratedRingTermRepresentative ys y) rfl
    exact h.trans (folkmanGeneratedRingTermRepresentative_spec ys y)
  map_add' x y := by
    apply Subtype.ext
    let t := folkmanGeneratedRingTermRepresentative xs x
    let u := folkmanGeneratedRingTermRepresentative xs y
    have ht : (.add t u : FolkmanRingTerm n).eval xs = (x + y).val := by
      change t.eval xs + u.eval xs = x.val + y.val
      rw [folkmanGeneratedRingTermRepresentative_spec,
        folkmanGeneratedRingTermRepresentative_spec]
    have htx : (folkmanGeneratedRingTermMap xs ys x).val = t.eval ys :=
      folkmanGeneratedRingTermMap_eval xs ys hEq x t
        (folkmanGeneratedRingTermRepresentative_spec xs x)
    have huy : (folkmanGeneratedRingTermMap xs ys y).val = u.eval ys :=
      folkmanGeneratedRingTermMap_eval xs ys hEq y u
        (folkmanGeneratedRingTermRepresentative_spec xs y)
    change (folkmanGeneratedRingTermMap xs ys (x + y)).val =
      (folkmanGeneratedRingTermMap xs ys x).val +
      (folkmanGeneratedRingTermMap xs ys y).val
    calc
      (folkmanGeneratedRingTermMap xs ys (x + y)).val =
          (.add t u : FolkmanRingTerm n).eval ys :=
        folkmanGeneratedRingTermMap_eval xs ys hEq (x + y) (.add t u) ht
      _ = t.eval ys + u.eval ys := rfl
      _ = (folkmanGeneratedRingTermMap xs ys x).val +
          (folkmanGeneratedRingTermMap xs ys y).val := by rw [htx, huy]
  map_mul' x y := by
    apply Subtype.ext
    let t := folkmanGeneratedRingTermRepresentative xs x
    let u := folkmanGeneratedRingTermRepresentative xs y
    have ht : (.mul t u : FolkmanRingTerm n).eval xs = (x * y).val := by
      change t.eval xs * u.eval xs = x.val * y.val
      rw [folkmanGeneratedRingTermRepresentative_spec,
        folkmanGeneratedRingTermRepresentative_spec]
    have htx : (folkmanGeneratedRingTermMap xs ys x).val = t.eval ys :=
      folkmanGeneratedRingTermMap_eval xs ys hEq x t
        (folkmanGeneratedRingTermRepresentative_spec xs x)
    have huy : (folkmanGeneratedRingTermMap xs ys y).val = u.eval ys :=
      folkmanGeneratedRingTermMap_eval xs ys hEq y u
        (folkmanGeneratedRingTermRepresentative_spec xs y)
    change (folkmanGeneratedRingTermMap xs ys (x * y)).val =
      (folkmanGeneratedRingTermMap xs ys x).val *
      (folkmanGeneratedRingTermMap xs ys y).val
    calc
      (folkmanGeneratedRingTermMap xs ys (x * y)).val =
          (.mul t u : FolkmanRingTerm n).eval ys :=
        folkmanGeneratedRingTermMap_eval xs ys hEq (x * y) (.mul t u) ht
      _ = t.eval ys * u.eval ys := rfl
      _ = (folkmanGeneratedRingTermMap xs ys x).val *
          (folkmanGeneratedRingTermMap xs ys y).val := by rw [htx, huy]

/-- The isomorphism interprets the same term in the target tuple. -/
theorem folkmanGeneratedNonunitalRingEquiv_eval_term
    {n : ℕ} {α β : Type*} [BooleanRing α] [BooleanRing β]
    (xs : Fin n → α) (ys : Fin n → β)
    (hEq : ∀ t u : FolkmanRingTerm n,
      t.eval xs = u.eval xs ↔ t.eval ys = u.eval ys)
    (x : folkmanGeneratedNonunitalSubring xs)
    (t : FolkmanRingTerm n) (ht : t.eval xs = x.val) :
    (folkmanGeneratedNonunitalRingEquiv_of_termEqualities xs ys hEq x).val =
      t.eval ys :=
  folkmanGeneratedRingTermMap_eval xs ys hEq x t ht

/-- The distinguished generators are preserved. -/
theorem folkmanGeneratedNonunitalRingEquiv_generator
    {n : ℕ} {α β : Type*} [BooleanRing α] [BooleanRing β]
    (xs : Fin n → α) (ys : Fin n → β)
    (hEq : ∀ t u : FolkmanRingTerm n,
      t.eval xs = u.eval xs ↔ t.eval ys = u.eval ys)
    (i : Fin n) :
    (folkmanGeneratedNonunitalRingEquiv_of_termEqualities xs ys hEq
      ⟨xs i, (.generator i : FolkmanRingTerm n).eval_mem_generated xs⟩).val =
        ys i :=
  folkmanGeneratedNonunitalRingEquiv_eval_term xs ys hEq _ (.generator i) rfl

/-- Equal nonzero signatures determine all equations in genuine ring syntax. -/
theorem folkmanRingTerm_equalities_of_patterns_eq
    {n atomsA atomsB : ℕ}
    (xs : Fin n → Finset (Fin atomsA))
    (ys : Fin n → Finset (Fin atomsB))
    (h : folkmanTupleNonzeroPatterns xs = folkmanTupleNonzeroPatterns ys)
    (t u : FolkmanRingTerm n) :
    t.evalSet xs = u.evalSet xs ↔ t.evalSet ys = u.evalSet ys := by
  have heq := folkmanNonunitalTerm_equalities_of_patterns_eq
    xs ys h t.toNonunitalTerm u.toNonunitalTerm
  simpa only [FolkmanRingTerm.toNonunitalTerm_evalSet] using heq

/-- The same equality kernel on the native powerset-ring carriers. -/
theorem folkmanRingTerm_nativeEqualities_of_patterns_eq
    {n atomsA atomsB : ℕ}
    (xs : Fin n → Finset (Fin atomsA))
    (ys : Fin n → Finset (Fin atomsB))
    (h : folkmanTupleNonzeroPatterns xs = folkmanTupleNonzeroPatterns ys)
    (t u : FolkmanRingTerm n) :
    t.eval (fun i => toBoolRing (xs i)) =
        u.eval (fun i => toBoolRing (xs i)) ↔
      t.eval (fun i => toBoolRing (ys i)) =
        u.eval (fun i => toBoolRing (ys i)) := by
  simp only [FolkmanRingTerm.eval_toBoolRing, toBoolRing_inj]
  exact folkmanRingTerm_equalities_of_patterns_eq xs ys h t u

/-- Profile-induced isomorphism of actual generated non-unital powerset rings. -/
noncomputable def folkmanGeneratedNonunitalRingEquiv_of_patterns_eq
    {n atomsA atomsB : ℕ}
    (xs : Fin n → Finset (Fin atomsA))
    (ys : Fin n → Finset (Fin atomsB))
    (h : folkmanTupleNonzeroPatterns xs = folkmanTupleNonzeroPatterns ys) :
    folkmanGeneratedNonunitalSubring (fun i => toBoolRing (xs i)) ≃+*
      folkmanGeneratedNonunitalSubring (fun i => toBoolRing (ys i)) :=
  folkmanGeneratedNonunitalRingEquiv_of_termEqualities
    (fun i => toBoolRing (xs i)) (fun i => toBoolRing (ys i))
    (folkmanRingTerm_nativeEqualities_of_patterns_eq xs ys h)

end SuccessorTree.NonPrecompact
