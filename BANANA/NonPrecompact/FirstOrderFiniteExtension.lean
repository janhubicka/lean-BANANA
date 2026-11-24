import Mathlib.ModelTheory.Fraisse

/-!
# First-order ultrahomogeneity from finite extensions

A locally finite model can use its finite extension property directly with
mathlib's back-and-forth theorem for finitely generated substructures.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

/-- In a countable locally finite structure, extension of embeddings along
inclusions of finite substructures implies ultrahomogeneity. -/
theorem isUltrahomogeneous_of_finite_extension
    {L : Language} {M : Type*} [L.Structure M] [Countable M]
    (finite_fg : ∀ S : L.Substructure M, S.FG → Finite S)
    (extend : ∀ (S T : L.Substructure M) (hST : S ≤ T),
      Finite S → Finite T → ∀ f : S ↪[L] M,
        ∃ g : T ↪[L] M, g.comp (S.inclusion hST) = f) :
    L.IsUltrahomogeneous M := by
  apply (Language.isUltrahomogeneous_iff_IsExtensionPair (L := L)
    (Language.Structure.cg_of_countable (L := L) (M := M))).2
  rintro ⟨f, hfg⟩ x
  let T := f.dom ⊔ Language.Substructure.closure L {x}
  have hST : f.dom ≤ T := le_sup_left
  have hTfg : T.FG := hfg.sup (Language.Substructure.fg_closure_singleton x)
  obtain ⟨g, hg⟩ := extend f.dom T hST (finite_fg f.dom hfg) (finite_fg T hTfg)
    (f.cod.subtype.comp f.toEquiv.toEmbedding)
  refine ⟨⟨⟨T, g.toHom.range, g.equivRange⟩, hTfg⟩, ?_, ⟨hST, ?_⟩⟩
  · have hclosure : (Language.Substructure.closure L {x} : Set M) ⊆ (T : Set M) :=
      SetLike.coe_subset_coe.mpr le_sup_right
    exact hclosure (Language.Substructure.subset_closure (Set.mem_singleton x))
  · ext a
    exact DFunLike.congr_fun hg a

end SuccessorTree.NonPrecompact
