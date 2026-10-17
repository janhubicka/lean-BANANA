import BANANA.NonPrecompact.PrebananaFiveAryFiniteExtensionSquare
import BANANA.NonPrecompact.PrebananaAbstractModelPowersetEmbedding

/-!
# Every finite marked pre-BANANA Boolean algebra embeds in a five-ary stage

A useful consequence of the already verified finite powerset
extension square is that the explicit five-ary tower contains an
isomorphic copy of every finite marked Boolean algebra.

There is only one atom at stage zero, of total F₂ mark zero.
Every abstract finite marked Boolean algebra has zero total atom
mark, so the finite-extension square over the one-point atom
partition embeds its entire atom powerset into the stage of depth
equal to its number of atoms. The canonical marked powerset
representation converts this to a genuine embedding of the
original Boolean algebra, preserving every Boolean operation
and the unary marking.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- Each finite nontrivial marked Boolean algebra embeds into
an explicit finite stage of the five-ary tower, at a depth bounded
by the number of its atoms. -/
theorem prebananaFiveAry_everyFiniteModel_embeds
    (B : PrebananaFiniteBooleanModel) :
    ∃ n : ℕ, Nonempty
      (PrebananaFiniteBooleanEmbedding B
        (prebananaFiveAryBooleanStage n)) := by
  classical
  let β := PrebananaAbstractAtoms B.carrier
  letI : Nonempty β := prebananaAbstractAtoms_nonempty B.carrier
  let markB : β → F2 := fun b => B.μ (b : B.carrier)
  have htotal : (∑ b : β, markB b) = 0 :=
    prebananaAbstractParity_total_even_on_atoms
      B.carrier B.μ B.μ_bot B.μ_top B.μ_add
  let source : PrebananaFiveAryWord 0 → Unit := fun _ => ()
  let target : β → Unit := fun _ => ()
  have hsource : Function.Surjective source := by
    intro d
    cases d
    exact ⟨fun _ => 0, rfl⟩
  have htarget : Function.Surjective target := by
    intro d
    cases d
    exact ⟨Classical.choice (inferInstance : Nonempty β), rfl⟩
  have hlocal : ∀ d : Unit,
      (∑ w : PrebananaFiveAryWord 0,
        if source w = d then prebananaFiveAryWordMark 0 w else 0) =
      ∑ b : β, if target b = d then markB b else 0 := by
    intro d
    cases d
    simpa [source, target, htotal] using
      (prebananaFiveAryWordMark_total 0)
  obtain ⟨g, _⟩ :=
    prebananaFiveAry_finiteExtensionSquare
      0 β Unit source target hsource htarget markB htotal hlocal
  let code : PrebananaFiniteBooleanEmbedding B
      (prebananaFiniteMarkedPowerset β markB htotal) :=
    prebananaAbstractModel_markedPowersetEmbedding B
  refine ⟨Fintype.card β, ?_⟩
  exact ⟨by simpa using (g.comp code)⟩

end SuccessorTree.NonPrecompact
