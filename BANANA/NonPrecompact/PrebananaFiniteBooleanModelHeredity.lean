import BANANA.NonPrecompact.PrebananaFiniteBooleanModelSkeleton

/-!
# Heredity of the actual finite marked Boolean class

Every Boolean subalgebra of a finite nontrivial marked Boolean algebra
inherits the F₂ marking, the zero and top conditions, and the
disjoint-additivity law. The inclusion is a genuine marking-preserving
bounded-lattice embedding.

This is the hereditary ingredient of the pre-BANANA Fraïssé class
argument. It is stronger than closure only under tuple-generated
subalgebras, but makes no claim about the countable limit.
-/

namespace SuccessorTree.NonPrecompact

/-- Restriction of an admissibly marked finite Boolean algebra to
any Boolean subalgebra is again a finite marked Boolean model. -/
noncomputable def prebananaFiniteBooleanSubmodel
    (A : PrebananaFiniteBooleanModel)
    (S : BooleanSubalgebra A.carrier) :
    PrebananaFiniteBooleanModel where
  carrier := S
  booleanAlgebra := inferInstance
  finite := by
    classical
    exact Fintype.ofFinite _
  nontrivial := by
    refine ⟨(⊥ : S), (⊤ : S), ?_⟩
    intro h
    have hval : (⊥ : A.carrier) = ⊤ := congrArg Subtype.val h
    exact (bot_ne_top : (⊥ : A.carrier) ≠ ⊤) hval
  μ := fun x => A.μ x.val
  μ_bot := A.μ_bot
  μ_top := A.μ_top
  μ_add := by
    intro x y hxy
    change A.μ (x.val ⊔ y.val) = A.μ x.val + A.μ y.val
    apply A.μ_add
    exact congrArg Subtype.val hxy

/-- Boolean-subalgebra inclusion preserves the entire pre-BANANA
functional language and the unary marking. -/
def prebananaFiniteBooleanSubmodel_embedding
    (A : PrebananaFiniteBooleanModel)
    (S : BooleanSubalgebra A.carrier) :
    PrebananaFiniteBooleanEmbedding
      (prebananaFiniteBooleanSubmodel A S) A where
  hom := {
    toFun := fun x => x.val
    map_bot' := rfl
    map_top' := rfl
    map_sup' := by intro x y; rfl
    map_inf' := by intro x y; rfl
  }
  injective := Subtype.val_injective
  preserves_μ := by intro x; rfl

end SuccessorTree.NonPrecompact
