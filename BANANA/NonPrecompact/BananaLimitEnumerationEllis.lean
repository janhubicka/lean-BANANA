import BANANA.NonPrecompact.BananaLimitDefinableColouring
import BANANA.NonPrecompact.FirstOrderFiniteParameterRealisation
import BANANA.NonPrecompact.FirstOrderEnumerationEllis

/-!
# An invariant Ellis map for the tagged BANANA limit

The finite tuple orbits supply both finite-parameter type realisation
and strong finite homogeneity. The checked definable Ramsey property
therefore gives an Ellis map with invariant values on realised types.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder
open Set

private theorem bananaLimit_finite_type_covers :
    ∀ n : ℕ, ∃ R : Finset (Fin n → BananaTaggedCarrier),
      ∀ b : Fin n → BananaTaggedCarrier,
        ∃ a : R, SameFormulaType (L := bananaTaggedLanguage) a.val b := by
  intro n
  obtain ⟨R, hR⟩ := bananaLimit_firstOrder_finite_tuple_orbit_representatives n
  exact ⟨R, formula_type_cover_of_finset_automorphism_orbit_representatives R hR⟩

/-- The tagged countable BANANA limit realises every complete finite tuple
type over finitely many parameters. -/
theorem bananaLimit_realizesFiniteParameterTypes :
    RealizesFiniteParameterTypes bananaTaggedLanguage BananaTaggedCarrier :=
  realizesFiniteParameterTypes_of_finite_type_covers bananaLimit_finite_type_covers

private theorem bananaLimit_stronglyFinitelyHomogeneous
    (n : ℕ) (x y : Fin n → BananaTaggedCarrier)
    (h : SameFormulaType (L := bananaTaggedLanguage) x y) :
    ∃ g : BananaTaggedCarrier ≃[bananaTaggedLanguage] BananaTaggedCarrier, g ∘ x = y := by
  obtain ⟨g, hg⟩ := exists_aut_of_sameFormulaType_of_finite_formula_type_covers
    bananaLimit_finite_type_covers h
  exact ⟨g.toEquiv, funext fun i => congrFun hg i⟩

/-- The Ellis semigroup of the tagged BANANA limit contains a map sending
every realised enumeration type to an invariant type. -/
theorem bananaLimit_exists_invariantEnumerationEllisMap :
    ∃ η : EnumerationTypeSpace bananaTaggedLanguage BananaTaggedCarrier →
        EnumerationTypeSpace bananaTaggedLanguage BananaTaggedCarrier,
      η ∈ closure (range (enumerationTypeSpaceAction bananaLimit_realizesFiniteParameterTypes
        bananaLimit_stronglyFinitelyHomogeneous)) ∧
      ∀ (x : BananaTaggedCarrier → BananaTaggedCarrier)
        (hx : ExtendsEnumerationType ((bananaTaggedLanguage.elementaryDiagram
          BananaTaggedCarrier).typeOf x)),
        IsAutomorphismInvariantType (η ⟨(bananaTaggedLanguage.elementaryDiagram
          BananaTaggedCarrier).typeOf x, hx⟩).val :=
  (hasDefinableTupleRamsey_iff_exists_ellisMap bananaLimit_realizesFiniteParameterTypes
    bananaLimit_stronglyFinitelyHomogeneous).mp
      (bananaTagged_completeTheory_hasDefinableTupleRamsey BananaTaggedCarrier)

end SuccessorTree.NonPrecompact
