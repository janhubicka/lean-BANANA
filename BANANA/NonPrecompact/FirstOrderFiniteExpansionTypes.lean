import BANANA.NonPrecompact.FirstOrderExpansionRestriction
import Mathlib.Basic.Finite.Sigma

/-!
# Finiteness of labelled expansions

On a fixed finite carrier, finiteness of the isomorphism types of any
family of expansions implies finiteness of the family of labelled
structures. Within each type, a chosen isomorphism to a representative
determines the source structure from its underlying function.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

universe u v w

variable {L : Language.{u, v}} {M : Type w}

/-- Isomorphism of first-order structures on a fixed carrier. -/
def firstOrderStructureIsomorphismSetoid (S : Set (L.Structure M)) : Setoid S where
  r a b := Nonempty (@Language.Equiv L M M a.val b.val)
  iseqv := {
    refl := fun a => ⟨@Language.Equiv.refl L M a.val⟩
    symm := by
      rintro a b ⟨e⟩
      exact ⟨@Language.Equiv.symm L M M a.val b.val e⟩
    trans := by
      rintro a b c ⟨e⟩ ⟨g⟩
      exact ⟨@Language.Equiv.comp L M M a.val b.val M c.val g e⟩ }

/-- Finite precompactness up to isomorphism implies finitely many choices
of expansion on each fixed finite reduct carrier. -/
theorem finite_firstOrderStructures_of_finite_isomorphism_types (S : Set (L.Structure M))
    [Finite M] [Finite (Quotient (firstOrderStructureIsomorphismSetoid S))] : Finite S := by
  classical
  let Q := Quotient (firstOrderStructureIsomorphismSetoid S)
  let mk : S → Q := Quotient.mk _
  let _ (q : Q) : Finite {a : S // mk a = q} := by
    let rep : S := Quotient.out q
    let iso (a : {a : S // mk a = q}) : @Language.Equiv L M M a.val.val rep.val :=
      Classical.choice (Quotient.exact (a.property.trans (Quotient.out_eq q).symm))
    let code (a : {a : S // mk a = q}) : M → M :=
      @Language.Equiv.toEquiv L M M a.val.val rep.val (iso a)
    apply Finite.of_injective code
    intro a b eq
    apply Subtype.ext
    apply Subtype.ext
    let _ : L.Structure M := rep.val
    exact firstOrderExpansion_eq_of_embeddings
      (@Language.Equiv.toEmbedding L M M a.val.val rep.val (iso a))
      (@Language.Equiv.toEmbedding L M M b.val.val rep.val (iso b)) (congrFun eq)
  exact Finite.of_equiv _ (Equiv.sigmaFiberEquiv mk)

end SuccessorTree.NonPrecompact
