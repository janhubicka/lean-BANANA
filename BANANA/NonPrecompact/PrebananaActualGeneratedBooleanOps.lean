import BANANA.NonPrecompact.PrebananaAbstractGeneratedBooleanOperations
import BANANA.NonPrecompact.PrebananaGeneratedBooleanClosure

/-!
# Boolean operations on the actual generated pre-BANANA subalgebras

The previously checked term-range isomorphism preserves Boolean operations,
and the generated-subalgebra bridge identifies the term range with the actual
Mathlib `BooleanSubalgebra.closure`.  Here we transport the operation laws
to those genuine subalgebras, without identifying a generated algebra with
an arbitrary set of atoms.

This is a finite-generated-substructure interface.  It does not construct
the countable Fraïssé limit, prove its homogeneity, or establish
ω-categoricity by itself.
-/

namespace SuccessorTree.NonPrecompact

variable {n : ℕ} {α β : Type*}
variable [BooleanAlgebra α] [BooleanAlgebra β]
variable {tupleA : Fin n → α} {tupleB : Fin n → β}
variable {μA : α → F2} {μB : β → F2}

/-- The generated-subalgebra equivalence maps each concrete term value
to the value of the same term at the target generators. -/
theorem PrebananaAbstractGeneratedMarkedIso.toGeneratedEquiv_map_term
    (e : PrebananaAbstractGeneratedMarkedIso α β tupleA tupleB μA μB)
    (t : PrebananaBooleanTerm n) :
    (e.toGeneratedEquiv
      (⟨t.evalBoolean tupleA,
        (prebananaGeneratedBooleanSubalgebra_mem_iff α tupleA _).mpr
          ⟨t, rfl⟩⟩ : prebananaGeneratedBooleanSubalgebra α tupleA)).val =
      t.evalBoolean tupleB := by
  change (e.equiv
    (⟨t.evalBoolean tupleA, ⟨t, rfl⟩⟩ :
      prebananaAbstractTermRange α tupleA)).val =
    t.evalBoolean tupleB
  exact e.map_term t

/-- The map preserves the least element of the actual Boolean subalgebra. -/
theorem PrebananaAbstractGeneratedMarkedIso.toGeneratedEquiv_bot_val
    (e : PrebananaAbstractGeneratedMarkedIso α β tupleA tupleB μA μB) :
    (e.toGeneratedEquiv
      (⊥ : prebananaGeneratedBooleanSubalgebra α tupleA)).val =
      (⊥ : β) := by
  let E := prebananaAbstractTermRangeEquivGenerated α tupleA
  have h : E.symm (⊥ : prebananaGeneratedBooleanSubalgebra α tupleA) =
      prebananaAbstractTermRange_zero α tupleA := by
    apply Subtype.ext
    rfl
  calc
    (e.toGeneratedEquiv
        (⊥ : prebananaGeneratedBooleanSubalgebra α tupleA)).val =
      (e.equiv (E.symm (⊥ : prebananaGeneratedBooleanSubalgebra α tupleA))).val := rfl
    _ = (e.equiv (prebananaAbstractTermRange_zero α tupleA)).val :=
      congrArg (fun x : prebananaAbstractTermRange α tupleA => (e.equiv x).val) h
    _ = (⊥ : β) := e.map_zero

/-- The map preserves the greatest element of the actual Boolean subalgebra. -/
theorem PrebananaAbstractGeneratedMarkedIso.toGeneratedEquiv_top_val
    (e : PrebananaAbstractGeneratedMarkedIso α β tupleA tupleB μA μB) :
    (e.toGeneratedEquiv
      (⊤ : prebananaGeneratedBooleanSubalgebra α tupleA)).val =
      (⊤ : β) := by
  let E := prebananaAbstractTermRangeEquivGenerated α tupleA
  have h : E.symm (⊤ : prebananaGeneratedBooleanSubalgebra α tupleA) =
      prebananaAbstractTermRange_one α tupleA := by
    apply Subtype.ext
    rfl
  calc
    (e.toGeneratedEquiv
        (⊤ : prebananaGeneratedBooleanSubalgebra α tupleA)).val =
      (e.equiv (E.symm (⊤ : prebananaGeneratedBooleanSubalgebra α tupleA))).val := rfl
    _ = (e.equiv (prebananaAbstractTermRange_one α tupleA)).val :=
      congrArg (fun x : prebananaAbstractTermRange α tupleA => (e.equiv x).val) h
    _ = (⊤ : β) := e.map_one

/-- The map preserves complements in the actual generated subalgebras. -/
theorem PrebananaAbstractGeneratedMarkedIso.toGeneratedEquiv_compl_val
    (e : PrebananaAbstractGeneratedMarkedIso α β tupleA tupleB μA μB)
    (x : prebananaGeneratedBooleanSubalgebra α tupleA) :
    (e.toGeneratedEquiv xᶜ).val = (e.toGeneratedEquiv x).valᶜ := by
  let E := prebananaAbstractTermRangeEquivGenerated α tupleA
  have h : E.symm xᶜ =
      prebananaAbstractTermRange_complement α tupleA (E.symm x) := by
    apply Subtype.ext
    rfl
  calc
    (e.toGeneratedEquiv xᶜ).val = (e.equiv (E.symm xᶜ)).val := rfl
    _ = (e.equiv (prebananaAbstractTermRange_complement α tupleA (E.symm x))).val :=
      congrArg (fun z : prebananaAbstractTermRange α tupleA => (e.equiv z).val) h
    _ = (e.equiv (E.symm x)).valᶜ := e.map_complement (E.symm x)
    _ = (e.toGeneratedEquiv x).valᶜ := rfl

/-- The map preserves joins in the actual generated subalgebras. -/
theorem PrebananaAbstractGeneratedMarkedIso.toGeneratedEquiv_sup_val
    (e : PrebananaAbstractGeneratedMarkedIso α β tupleA tupleB μA μB)
    (x y : prebananaGeneratedBooleanSubalgebra α tupleA) :
    (e.toGeneratedEquiv (x ⊔ y)).val =
      (e.toGeneratedEquiv x).val ⊔ (e.toGeneratedEquiv y).val := by
  let E := prebananaAbstractTermRangeEquivGenerated α tupleA
  have h : E.symm (x ⊔ y) =
      prebananaAbstractTermRange_join α tupleA (E.symm x) (E.symm y) := by
    apply Subtype.ext
    rfl
  calc
    (e.toGeneratedEquiv (x ⊔ y)).val =
        (e.equiv (E.symm (x ⊔ y))).val := rfl
    _ = (e.equiv (prebananaAbstractTermRange_join α tupleA
        (E.symm x) (E.symm y))).val :=
          congrArg (fun z : prebananaAbstractTermRange α tupleA => (e.equiv z).val) h
    _ = (e.equiv (E.symm x)).val ⊔ (e.equiv (E.symm y)).val :=
          e.map_join (E.symm x) (E.symm y)
    _ = (e.toGeneratedEquiv x).val ⊔ (e.toGeneratedEquiv y).val := rfl

/-- The map preserves meets in the actual generated subalgebras. -/
theorem PrebananaAbstractGeneratedMarkedIso.toGeneratedEquiv_inf_val
    (e : PrebananaAbstractGeneratedMarkedIso α β tupleA tupleB μA μB)
    (x y : prebananaGeneratedBooleanSubalgebra α tupleA) :
    (e.toGeneratedEquiv (x ⊓ y)).val =
      (e.toGeneratedEquiv x).val ⊓ (e.toGeneratedEquiv y).val := by
  let E := prebananaAbstractTermRangeEquivGenerated α tupleA
  have h : E.symm (x ⊓ y) =
      prebananaAbstractTermRange_meet α tupleA (E.symm x) (E.symm y) := by
    apply Subtype.ext
    rfl
  calc
    (e.toGeneratedEquiv (x ⊓ y)).val =
        (e.equiv (E.symm (x ⊓ y))).val := rfl
    _ = (e.equiv (prebananaAbstractTermRange_meet α tupleA
        (E.symm x) (E.symm y))).val :=
          congrArg (fun z : prebananaAbstractTermRange α tupleA => (e.equiv z).val) h
    _ = (e.equiv (E.symm x)).val ⊓ (e.equiv (E.symm y)).val :=
          e.map_meet (E.symm x) (E.symm y)
    _ = (e.toGeneratedEquiv x).val ⊓ (e.toGeneratedEquiv y).val := rfl

/-- These are genuine equalities in the generated Boolean subalgebras,
rather than only equations for values in the ambient Boolean algebras. -/
theorem PrebananaAbstractGeneratedMarkedIso.toGeneratedEquiv_map_bot
    (e : PrebananaAbstractGeneratedMarkedIso α β tupleA tupleB μA μB) :
    e.toGeneratedEquiv (⊥ : prebananaGeneratedBooleanSubalgebra α tupleA) =
      (⊥ : prebananaGeneratedBooleanSubalgebra β tupleB) := by
  apply Subtype.ext
  exact e.toGeneratedEquiv_bot_val

theorem PrebananaAbstractGeneratedMarkedIso.toGeneratedEquiv_map_top
    (e : PrebananaAbstractGeneratedMarkedIso α β tupleA tupleB μA μB) :
    e.toGeneratedEquiv (⊤ : prebananaGeneratedBooleanSubalgebra α tupleA) =
      (⊤ : prebananaGeneratedBooleanSubalgebra β tupleB) := by
  apply Subtype.ext
  exact e.toGeneratedEquiv_top_val

theorem PrebananaAbstractGeneratedMarkedIso.toGeneratedEquiv_map_compl
    (e : PrebananaAbstractGeneratedMarkedIso α β tupleA tupleB μA μB)
    (x : prebananaGeneratedBooleanSubalgebra α tupleA) :
    e.toGeneratedEquiv xᶜ = (e.toGeneratedEquiv x)ᶜ := by
  apply Subtype.ext
  exact e.toGeneratedEquiv_compl_val x

theorem PrebananaAbstractGeneratedMarkedIso.toGeneratedEquiv_map_sup
    (e : PrebananaAbstractGeneratedMarkedIso α β tupleA tupleB μA μB)
    (x y : prebananaGeneratedBooleanSubalgebra α tupleA) :
    e.toGeneratedEquiv (x ⊔ y) =
      e.toGeneratedEquiv x ⊔ e.toGeneratedEquiv y := by
  apply Subtype.ext
  exact e.toGeneratedEquiv_sup_val x y

theorem PrebananaAbstractGeneratedMarkedIso.toGeneratedEquiv_map_inf
    (e : PrebananaAbstractGeneratedMarkedIso α β tupleA tupleB μA μB)
    (x y : prebananaGeneratedBooleanSubalgebra α tupleA) :
    e.toGeneratedEquiv (x ⊓ y) =
      e.toGeneratedEquiv x ⊓ e.toGeneratedEquiv y := by
  apply Subtype.ext
  exact e.toGeneratedEquiv_inf_val x y

end SuccessorTree.NonPrecompact
