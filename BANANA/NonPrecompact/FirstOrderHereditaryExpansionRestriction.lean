import BANANA.NonPrecompact.FirstOrderExpansionRestriction
import Mathlib.ModelTheory.Fraisse

/-!
# Restrictions inside hereditary expansion classes

If a finite reduct embedding has expanded-substructure range, its
induced expansion remains in the hereditary class. For a language map
which adds only relations, this yields restrictions along all reduct
embeddings into every member of the expansion class.
-/

namespace SuccessorTree.NonPrecompact

open CategoryTheory FirstOrder Function
open scoped FirstOrder

universe u v u' v' w

variable {L : Language.{u, v}} {L' : Language.{u', v'}}
  {M N : Type w} [L.Structure M] [L.Structure N] [T : L'.Structure N]

/-- A compatible restriction of a finite structure belongs to the same
hereditary class as the expanded target. -/
theorem restrictFirstOrderExpansion_mem_of_hereditary [Finite M]
    {K : Set (Bundled.{w} L'.Structure)} (hK : Language.Hereditary K)
    (hN : Bundled.mk N T ∈ K) (e : M ↪[L] N) (h : ExpandedRangeClosed (L' := L') e) :
    Bundled.mk M (restrictFirstOrderExpansion e h) ∈ K := by
  let _ : L'.Structure M := restrictFirstOrderExpansion e h
  exact hK ⟨N, T⟩ hN
    ⟨Language.Structure.FG.of_finite, ⟨restrictFirstOrderExpansion_embedding e h⟩⟩

/-- Every reduct embedding into a hereditary expansion with no added
functions induces an expansion in the same class. -/
theorem exists_hereditary_restriction_of_onFunction_surjective [Finite M]
    {K : Set (Bundled.{w} L'.Structure)} (hK : Language.Hereditary K)
    (hN : Bundled.mk N T ∈ K) (φ : L →ᴸ L') [φ.IsExpansionOn N]
    (hφ : ∀ n, Surjective (fun f : L.Functions n => φ.onFunction f))
    (e : M ↪[L] N) :
    ∃ (S : L'.Structure M), Bundled.mk M S ∈ K ∧
      (@Language.LHom.IsExpansionOn L L' φ M _ S) ∧
      ∃ (g : @Language.Embedding L' M N S T),
        ∀ x, (@Language.Embedding.toEmbedding L' M N S T g) x = e x := by
  let h := expandedRangeClosed_of_onFunction_surjective φ hφ e
  exact ⟨restrictFirstOrderExpansion e h,
    restrictFirstOrderExpansion_mem_of_hereditary hK hN e h,
    restrictFirstOrderExpansion_isExpansionOn φ e h,
    restrictFirstOrderExpansion_embedding e h, fun _ => rfl⟩

end SuccessorTree.NonPrecompact
