import BANANA.NonPrecompact.PrebananaFiniteBooleanModelStrongAP
import BANANA.NonPrecompact.PrebananaFiniteJEP
import BANANA.NonPrecompact.PrebananaCanonicalFaithfulCodes

/-!
# Joint embedding for the actual finite marked Boolean class

The finite atom-presentation class has joint embedding. Every nontrivial
finite Boolean algebra with admissible F₂ marking is canonically a
marked powerset of its atoms. Composing both faithful codes with the
atom-class joint embeddings gives marked Boolean embeddings into
one common finite Boolean model.

This is a class-level joint embedding statement rather than a statement
only about coordinate presentations. It does not construct the countable
Fraïssé limit.
-/

namespace SuccessorTree.NonPrecompact

/-- Two arbitrary finite nontrivial marked Boolean algebras jointly
embed into a third finite marked Boolean algebra. -/
theorem prebananaFiniteBooleanModel_jointEmbedding
    (B C : PrebananaFiniteBooleanModel) :
    ∃ D : PrebananaFiniteBooleanModel,
      Nonempty (PrebananaFiniteBooleanEmbedding B D) ∧
      Nonempty (PrebananaFiniteBooleanEmbedding C D) := by
  classical
  let Bcode :=
    prebananaAbstractAtomCode B.carrier B.μ B.μ_bot B.μ_top B.μ_add
  let Ccode :=
    prebananaAbstractAtomCode C.carrier C.μ C.μ_bot C.μ_top C.μ_add
  let CB :=
    prebananaCanonicalFaithfulFiniteCode
      B.carrier B.μ B.μ_bot B.μ_top B.μ_add
  let CC :=
    prebananaCanonicalFaithfulFiniteCode
      C.carrier C.μ C.μ_bot C.μ_top C.μ_add
  obtain ⟨D, ⟨f⟩, ⟨g⟩⟩ :=
    prebananaAtomClass_joint_embedding Bcode Ccode
  obtain ⟨hB, _, hinjB, hbotB, htopB, hsupB, hinfB, hmarkB⟩ :=
    prebananaCodedBooleanEmbedding_properties
      Bcode D f CB.toFun B.μ
      CB.injective CB.map_bot CB.map_top
      CB.map_sup CB.map_inf CB.map_parity
  obtain ⟨hC, _, hinjC, hbotC, htopC, hsupC, hinfC, hmarkC⟩ :=
    prebananaCodedBooleanEmbedding_properties
      Ccode D g CC.toFun C.μ
      CC.injective CC.map_bot CC.map_top
      CC.map_sup CC.map_inf CC.map_parity
  let FB : PrebananaMarkedFiniteMap B.carrier D B.μ := {
    toFun := hB
    injective := hinjB
    map_bot := hbotB
    map_top := htopB
    map_sup := hsupB
    map_inf := hinfB
    map_parity := hmarkB
  }
  let FC : PrebananaMarkedFiniteMap C.carrier D C.μ := {
    toFun := hC
    injective := hinjC
    map_bot := hbotC
    map_top := htopC
    map_sup := hsupC
    map_inf := hinfC
    map_parity := hmarkC
  }
  exact ⟨prebananaAtomFiniteBooleanModel D,
    ⟨FB.toFiniteBooleanEmbedding⟩,
    ⟨FC.toFiniteBooleanEmbedding⟩⟩

end SuccessorTree.NonPrecompact
