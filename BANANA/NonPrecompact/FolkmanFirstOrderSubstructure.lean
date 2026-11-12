import BANANA.NonPrecompact.FolkmanFirstOrderInterpretation
import Mathlib.ModelTheory.Substructures
import Mathlib.Tactic.FinCases

/-!
# Original non-unital subrings as tagged first-order substructures

For a two-sorted non-unital Folkman pairing, each pair of non-unital
subrings determines a first-order substructure of the tagged
one-sorted encoding. The carrier is the disjoint union of those
subrings, with two separate zero elements.

All four totalised ring operations preserve the carrier. The
pairing relation does not add closure requirements: it is simply
restricted to the existing carrier. No ambient unit is named.

This is the native-to-tagged direction of hereditary substructure
translation. The converse and generation/closure equality are
separate obligations, as is exact-head Lean verification.
-/

namespace SuccessorTree.NonPrecompact

open scoped FirstOrder

/-- The disjoint union of two non-unital subring carriers. -/
def folkmanTaggedSubringCarrier
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    (SL : NonUnitalSubring L) (SR : NonUnitalSubring R) :
    Set (Sum L R) :=
  fun z => match z with
    | .inl x => x ∈ SL
    | .inr y => y ∈ SR

/-- One pair of original non-unital subrings gives a substructure
of the complete tagged first-order language, independently of β. -/
noncomputable def folkmanTaggedSubstructure
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2)
    (SL : NonUnitalSubring L) (SR : NonUnitalSubring R) :
    @FirstOrder.Language.Substructure folkmanFirstOrderLanguage
      (Sum L R) (folkmanTaggedFirstOrderStructure L R β) := by
  classical
  letI : folkmanFirstOrderLanguage.Structure (Sum L R) :=
    folkmanTaggedFirstOrderStructure L R β
  refine {
    carrier := folkmanTaggedSubringCarrier SL SR
    fun_mem := ?_
  }
  intro n f args hargs
  by_cases hn0 : n = 0
  · subst n
    change Fin 2 at f
    fin_cases f
    · change (0 : L) ∈ SL
      exact SL.zero_mem
    · change (0 : R) ∈ SR
      exact SR.zero_mem
  · by_cases hn2 : n = 2
    · subst n
      change Fin 4 at f
      fin_cases f
      · cases hx : args 0 with
        | inl x =>
            cases hy : args 1 with
            | inl y =>
                change x + y ∈ SL
                apply SL.add_mem
                · simpa [folkmanTaggedSubringCarrier, hx] using hargs 0
                · simpa [folkmanTaggedSubringCarrier, hy] using hargs 1
            | inr _ =>
                change (0 : L) ∈ SL
                exact SL.zero_mem
        | inr _ =>
            change (0 : L) ∈ SL
            exact SL.zero_mem
      · cases hx : args 0 with
        | inl x =>
            cases hy : args 1 with
            | inl y =>
                change x * y ∈ SL
                apply SL.mul_mem
                · simpa [folkmanTaggedSubringCarrier, hx] using hargs 0
                · simpa [folkmanTaggedSubringCarrier, hy] using hargs 1
            | inr _ =>
                change (0 : L) ∈ SL
                exact SL.zero_mem
        | inr _ =>
            change (0 : L) ∈ SL
            exact SL.zero_mem
      · cases hx : args 0 with
        | inr x =>
            cases hy : args 1 with
            | inr y =>
                change x + y ∈ SR
                apply SR.add_mem
                · simpa [folkmanTaggedSubringCarrier, hx] using hargs 0
                · simpa [folkmanTaggedSubringCarrier, hy] using hargs 1
            | inl _ =>
                change (0 : R) ∈ SR
                exact SR.zero_mem
        | inl _ =>
            change (0 : R) ∈ SR
            exact SR.zero_mem
      · cases hx : args 0 with
        | inr x =>
            cases hy : args 1 with
            | inr y =>
                change x * y ∈ SR
                apply SR.mul_mem
                · simpa [folkmanTaggedSubringCarrier, hx] using hargs 0
                · simpa [folkmanTaggedSubringCarrier, hy] using hargs 1
            | inl _ =>
                change (0 : R) ∈ SR
                exact SR.zero_mem
        | inl _ =>
            change (0 : R) ∈ SR
            exact SR.zero_mem
    · have he : IsEmpty (folkmanFirstOrderLanguage.Functions n) := by
        change IsEmpty (folkmanFirstOrderFunctions n)
        simp [folkmanFirstOrderFunctions, hn0, hn2]
      exact isEmptyElim f

/-- Membership of a correctly tagged left element is exactly
membership in the original left non-unital subring. -/
theorem folkmanTaggedSubstructure_mem_inl
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2)
    (SL : NonUnitalSubring L) (SR : NonUnitalSubring R)
    (x : L) :
    (Sum.inl x : Sum L R) ∈ folkmanTaggedSubstructure β SL SR ↔
      x ∈ SL :=
  Iff.rfl

/-- The analogous right-sort membership equivalence. -/
theorem folkmanTaggedSubstructure_mem_inr
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2)
    (SL : NonUnitalSubring L) (SR : NonUnitalSubring R)
    (y : R) :
    (Sum.inr y : Sum L R) ∈ folkmanTaggedSubstructure β SL SR ↔
      y ∈ SR :=
  Iff.rfl

end SuccessorTree.NonPrecompact
