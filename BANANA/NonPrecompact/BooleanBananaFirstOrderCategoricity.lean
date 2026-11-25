import BANANA.NonPrecompact.FirstOrderOligomorphicCategoricity
import BANANA.NonPrecompact.PrebananaFiveAryCylinderMarkedOrbitFiniteness
import BANANA.NonPrecompact.PrebananaFiveAryCylinderInfinite

/-!
# Countable categoricity of the concrete Boolean–BANANA limit

The first-order structure is the existing cylinder Boolean algebra with a
unary predicate recording its nonzero mark. Its actual marked
automorphisms have finite tuple-orbit quotients, so the checked forward
implication of Ryll–Nardzewski gives countable categoricity.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open FirstOrder
open scoped FirstOrder

/-- The usual Boolean algebra operations in their first-order arities. -/
inductive BooleanFunctions : ℕ → Type
  | bot : BooleanFunctions 0
  | top : BooleanFunctions 0
  | inf : BooleanFunctions 2
  | sup : BooleanFunctions 2
  | compl : BooleanFunctions 1

/-- The marking predicate is true just on the elements with mark one. -/
inductive MarkRelations : ℕ → Type
  | marked : MarkRelations 1

/-- The Boolean algebra language with one unary marking predicate. -/
def markedBooleanLanguage : Language := ⟨BooleanFunctions, MarkRelations⟩

/-- Interpret the named operations and the marking on a Boolean algebra. -/
abbrev markedBooleanStructure (B : Type*) [BooleanAlgebra B] (μ : B → ZMod 2) :
    markedBooleanLanguage.Structure B where
  funMap
    | .bot, _ => ⊥
    | .top, _ => ⊤
    | .inf, x => x 0 ⊓ x 1
    | .sup, x => x 0 ⊔ x 1
    | .compl, x => (x 0)ᶜ
  RelMap
    | .marked, x => μ (x 0) = 1

variable {B : Type*} [BooleanAlgebra B] {μ : B → ZMod 2}

/-- A marked Boolean order automorphism is an automorphism in the
first-order marked Boolean algebra language. -/
def markedBooleanAutomorphism (E : B ≃o B) (hμ : ∀ b, μ (E b) = μ b) :
    letI := markedBooleanStructure B μ
    B ≃[markedBooleanLanguage] B :=
  letI := markedBooleanStructure B μ
  {
    toEquiv := E.toEquiv
    map_fun' := by
      intro n f x
      change E ((markedBooleanStructure B μ).funMap f x) =
        (markedBooleanStructure B μ).funMap f (E ∘ x)
      change BooleanFunctions n at f
      cases f with
      | bot => exact map_bot E
      | top => exact map_top E
      | inf => exact map_inf E _ _
      | sup => exact map_sup E _ _
      | compl => exact map_compl' (E : BoundedLatticeHom B B) _
    map_rel' := by
      intro n r x
      change MarkRelations n at r
      cases r
      change μ (E (x 0)) = 1 ↔ μ (x 0) = 1
      rw [hμ]
  }

noncomputable instance cylinderMarkedBooleanStructure :
    markedBooleanLanguage.Structure PrebananaFiveAryCylinderLimitCarrier :=
  markedBooleanStructure _ prebananaFiveAryCylinderMark

/-- Any two countably infinite models of the complete theory of the
first-order marked Boolean structure are isomorphic. -/
theorem cylinderMarkedBoolean_categorical_completeTheory :
    Cardinal.Categorical Cardinal.aleph0
      (markedBooleanLanguage.completeTheory PrebananaFiveAryCylinderLimitCarrier) := by
  apply categorical_completeTheory_of_finite_tupleOrbitQuotients
  intro n
  have : Finite (Quotient (prebananaCylinderMarkedOrbitSetoid n)) :=
    prebananaCylinderMarkedOrbit_finite n
  let f : Quotient (prebananaCylinderMarkedOrbitSetoid n) →
      Quotient (firstOrderTupleOrbit markedBooleanLanguage PrebananaFiveAryCylinderLimitCarrier n) :=
    Quotient.map id fun a b h => by
      obtain ⟨E, hμ, hcoord⟩ := h
      exact ⟨markedBooleanAutomorphism E hμ, hcoord⟩
  exact Finite.of_surjective f fun q =>
    Quotient.inductionOn q fun a => ⟨⟦a⟧, rfl⟩

/-- The concrete cylinder structure itself has countably infinite size,
so its complete theory has a model at the categorical cardinality. -/
theorem cylinderMarkedBoolean_card_aleph0 :
    Cardinal.mk PrebananaFiveAryCylinderLimitCarrier = Cardinal.aleph0 :=
  Cardinal.mk_eq_aleph0 PrebananaFiveAryCylinderLimitCarrier

end SuccessorTree.NonPrecompact.BooleanBanana
