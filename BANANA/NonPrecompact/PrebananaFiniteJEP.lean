import BANANA.NonPrecompact.PrebananaFiniteClass
import BANANA.NonPrecompact.PrebananaGridStrongAmalgam

/-!
# Joint embedding of finite pre-BANANA atom structures

The circulated pre-BANANA Fraïssé argument obtains the joint
embedding property by amalgamating over the two-element Boolean
algebra with zero marking. The atom representation has exactly
one unmarked atom for this base, and it embeds into every object.

This file packages that deduction using the existing kernel-checked
finite strong-amalgamation theorem. Countability and unbounded
finite atom counts were verified in `PrebananaFiniteClass`.
-/

namespace SuccessorTree.NonPrecompact

/-- Any two finite marked atom structures jointly embed in a
third one. Both morphisms preserve the parity marking on each
source atom fibre, hence on every Boolean element. -/
theorem prebananaAtomClass_joint_embedding
    (B C : PrebananaAtomStructure) :
    ∃ D : PrebananaAtomStructure,
      Nonempty (PrebananaAtomEmbedding B D) ∧
      Nonempty (PrebananaAtomEmbedding C D) := by
  obtain ⟨D, f, g, _, _⟩ :=
    exists_prebananaAtomStrongAmalgam
      (PrebananaAtomStructure.fromZeroBase B)
      (PrebananaAtomStructure.fromZeroBase C)
  exact ⟨D, ⟨f⟩, ⟨g⟩⟩

end SuccessorTree.NonPrecompact
