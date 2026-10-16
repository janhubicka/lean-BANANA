import BANANA.NonPrecompact.PrebananaFinitePowersetMarkedLifts
import BANANA.NonPrecompact.PrebananaFiveAryWordLevelAllocation

/-!
# Finite-extension diagram for the five-ary pre-BANANA tower

This is the commuting-square form of the finite extension lemma
in finite atom-powerset coordinates. An old finite marked
Boolean subalgebra is represented by a surjective atom map from
the level-n words to its base atoms. A prescribed extension is
represented by a surjective atom map from the new target atoms
to the same base atoms.

The finite-fibre marking equations are the precise expression of
both prescribed embeddings respecting the unary F₂ marking.

The new embedding is realised at the uniform depth equal to the
number of target atoms. Its inverse-image Boolean map agrees with
the iterated old-stage embedding on every base Boolean element.
Passage from arbitrary finite Boolean algebras to the canonical
atom presentations and construction of the countable direct limit
remain separate steps.
-/

namespace SuccessorTree.NonPrecompact

/-- A marked finite extension over a stage-n partition embeds into
the level n+|β| marked Boolean stage, commuting exactly with the old
base partition on all finite subsets of base atoms. -/
theorem prebananaFiveAry_finiteExtensionSquare
    (n : ℕ) (β : Type) (δ : Type*) [Fintype β]
    [DecidableEq β] [DecidableEq δ] [Nonempty β]
    (source : PrebananaFiveAryWord n → δ)
    (target : β → δ)
    (hsource : Function.Surjective source)
    (htarget : Function.Surjective target)
    (markB : β → F2)
    (htotal : (∑ b : β, markB b) = 0)
    (hlocal : ∀ d : δ,
      (∑ w : PrebananaFiveAryWord n,
        if source w = d then prebananaFiveAryWordMark n w else 0) =
      ∑ b : β, if target b = d then markB b else 0) :
    ∃ g : PrebananaFiniteBooleanEmbedding
        (prebananaFiniteMarkedPowerset β markB htotal)
        (prebananaFiveAryBooleanStage (n + Fintype.card β)),
      ∀ s : Finset δ,
        g.hom (Finset.univ.filter
          (fun b : β => target b ∈ s)) =
          Finset.univ.filter
            (fun w : PrebananaFiveAryWord (n + Fintype.card β) =>
              source ((Fin.appendEquiv n (Fintype.card β)).symm w).1 ∈ s) := by
  classical
  obtain ⟨part, hsurj, hcomm, hmark⟩ :=
    prebananaFiveAryWordLevel_markedAllocation n β δ
      source target hsource htarget markB hlocal
  let g : PrebananaFiniteBooleanEmbedding
      (prebananaFiniteMarkedPowerset β markB htotal)
      (prebananaFiveAryBooleanStage (n + Fintype.card β)) :=
    prebananaFiveAryOwnerMarkedEmbedding
      (n + Fintype.card β) β markB htotal part hsurj hmark
  refine ⟨g, ?_⟩
  intro s
  change
    (Finset.univ : Finset (PrebananaFiveAryWord (n + Fintype.card β))).filter
      (fun w => part w ∈
        (Finset.univ : Finset β).filter (fun b => target b ∈ s)) =
    (Finset.univ : Finset (PrebananaFiveAryWord (n + Fintype.card β))).filter
      (fun w =>
        source ((Fin.appendEquiv n (Fintype.card β)).symm w).1 ∈ s)
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hcomm w]

end SuccessorTree.NonPrecompact
