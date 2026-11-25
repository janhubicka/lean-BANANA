import BANANA.NonPrecompact.FolkmanFirstOrderLanguage
import BANANA.NonPrecompact.FolkmanNativePairingEmbedding
import Mathlib.ModelTheory.Substructures

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

/-- The first-order encoding has exactly the original native embeddings. -/
noncomputable def folkmanNativePairingEmbeddingEquiv
    {L R L' R' : Type*} [BooleanRing L] [BooleanRing R] [BooleanRing L'] [BooleanRing R']
    (P : FolkmanNativeFinitePairing L R) (Q : FolkmanNativeFinitePairing L' R') :
    letI := folkmanProductStructure P.pairing
    letI := folkmanProductStructure Q.pairing
    FolkmanNativePairingEmbedding P Q ≃ ((L × R) ↪[folkmanLanguage] (L' × R')) := by
  letI := folkmanProductStructure P.pairing
  letI := folkmanProductStructure Q.pairing
  exact {
    toFun := fun f => folkmanProductEmbedding P.pairing Q.pairing f.left f.right
      f.left_injective f.right_injective f.preserves_pairing
    invFun := fun e => {
      left := folkmanProductEmbeddingLeft _ _ e
      right := folkmanProductEmbeddingRight _ _ e
      left_injective := folkmanProductEmbeddingLeft_injective _ _ e
      right_injective := folkmanProductEmbeddingRight_injective _ _ e
      preserves_pairing := folkmanProductEmbedding_preserves_pairing _ _ e }
    left_inv := by
      intro f
      cases f
      rfl
    right_inv := by
      intro e
      apply Language.Embedding.ext
      intro xy
      exact (folkmanProductEmbedding_split _ _ e xy).symm }

end SuccessorTree.NonPrecompact
