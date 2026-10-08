import BANANA.NonPrecompact.LinearBinaryRangeTransfer
import BANANA.NonPrecompact.LinearBinaryBoringExtension
import BANANA.NonPrecompact.LinearBinaryCanonicalPivot

/-!
# Representing all finite binary subspaces by exact successor coordinates

Induction on the ambient dimension. In the last-coordinate product
presentation, every subspace is either the graph of a linear functional
over its projection or the product of its projection with the final
one-dimensional coordinate space.

The graph case is realised by an exact boring-coordinate insertion.
The product case is realised by the canonical exact pivot extension.
The two extension lemmas use the dimension of the range to turn
containment into equality, avoiding a separate basis-selection proof.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

open Module

/-- The concrete row-echelon representation property for the linear
binary successor-tree model. -/
theorem everyBinarySubspaceRepresentable :
    EveryBinarySubspaceRepresentable := by
  intro d N
  induction N generalizing d with
  | zero =>
      intro P
      have hle :
          finrank F2 P.1 ≤ finrank F2 (Fin 0 → F2) :=
        Submodule.finrank_le P.1
      have hambient :
          finrank F2 (Fin 0 → F2) = 0 := by
        simp [Module.finrank_fintype_fun_eq_card]
      have hd : d = 0 := by
        rw [P.2, hambient] at hle
        omega
      subst d
      exact exactSubspace_representable_zero 0 P
  | succ n ih =>
      intro P
      let T := fixedSubspaceLastProduct P
      by_cases hv : ((0 : Fin n → F2), (1 : F2)) ∈ T.1
      · -- The last coordinate is an independent pivot.
        cases d with
        | zero =>
            have hrank :
                finrank F2 T.1 =
                  finrank F2 (T.1.map
                    (LinearMap.fst F2 (Fin n → F2) F2)) + 1 :=
              finrank_projected_of_pivot T.1 hv
            have hzero : finrank F2 T.1 = 0 := T.2
            omega
        | succ d =>
            let Q : FixedSubspace d n :=
              ⟨projectedSubspace P,
                projectedSubspace_finrank_pivot P hv⟩
            obtain ⟨f, hf⟩ := ih d Q
            refine ⟨extendExactWithPivot f, ?_⟩
            apply extendExactWithPivot_realises_product f P
            intro z
            have hQ : (exactSubspace f).1 = projectedSubspace P :=
              congrArg Subtype.val hf
            rw [hQ]
            have htransport := mem_fixedSubspaceLastProduct P z
            have hproduct :
                lastCoordinateLinearEquiv n z ∈ T.1 ↔
                  (lastCoordinateLinearEquiv n z).1 ∈
                    projectedSubspace P := by
              rw [subspace_eq_product_of_vertical T.1 hv]
              simp [projectedSubspace, T]
            exact htransport.trans hproduct
      · -- The last coordinate depends linearly on the preceding ones.
        let Q : FixedSubspace d n :=
          ⟨projectedSubspace P,
            projectedSubspace_finrank_boring P hv⟩
        obtain ⟨f, hf⟩ := ih d Q
        obtain ⟨e, he⟩ :=
          exists_linear_last_coordinate_of_injective T.1
            (firstCoordinate_injective_of_no_vertical T.1 hv)
        refine ⟨extendExactWithBoring f e, ?_⟩
        apply extendExactWithBoring_realises_graph f e P
        intro z
        have hQ : (exactSubspace f).1 = projectedSubspace P :=
          congrArg Subtype.val hf
        rw [hQ]
        have htransport := mem_fixedSubspaceLastProduct P z
        have hgraph :
            lastCoordinateLinearEquiv n z ∈ T.1 ↔
              (lastCoordinateLinearEquiv n z).1 ∈ projectedSubspace P ∧
              (lastCoordinateLinearEquiv n z).2 =
                e (lastCoordinateLinearEquiv n z).1 := by
          simpa [projectedSubspace, T] using
            (he (lastCoordinateLinearEquiv n z))
        exact htransport.trans hgraph

/-- Full binary subspace Ramsey follows from the concrete successor-tree
encoding, with no additional combinatorial hypothesis. -/
theorem binarySubspaceRamsey_via_successors :
    BinarySubspaceRamsey :=
  binarySubspaceRamsey_of_representable everyBinarySubspaceRepresentable

/-- One-sided copy-Ramsey degree one on the left sort, derived from the
successor-tree proof of binary subspace Ramsey. -/
theorem leftOneSidedCopyRamseyOne_via_successors (a : ℕ) :
    LeftOneSidedCopyRamseyOne a :=
  leftOneSidedCopyRamseyOne_of_representable
    everyBinarySubspaceRepresentable a

/-- One-sided copy-Ramsey degree one on the right sort. -/
theorem rightOneSidedCopyRamseyOne_via_successors (a : ℕ) :
    RightOneSidedCopyRamseyOne a :=
  rightOneSidedCopyRamseyOne_of_representable
    everyBinarySubspaceRepresentable a

end BinaryWord
end SuccessorTree.NonPrecompact
