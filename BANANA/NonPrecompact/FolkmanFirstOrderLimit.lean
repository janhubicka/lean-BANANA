import BANANA.NonPrecompact.FolkmanFirstOrderFraisse
import BANANA.NonPrecompact.FolkmanFirstOrderClass

/-!
# Finite native diagrams in the encoded Folkman limit

After supplying Fraïssé existence, the encoded limit admits every finite
native paired Boolean-ring structure. Its ultrahomogeneity extends a
native finite diagram using the original, possibly non-unital maps.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder CategoryTheory
open scoped FirstOrder

variable (M : Bundled.{0} folkmanLanguage.Structure) [Countable M]

/-- Every finite native paired Boolean ring embeds into a first-order
Fraïssé limit of the encoded class. -/
theorem folkmanFirstOrderLimit_nativeEmbeds
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M)
    {L R : Type} [BooleanRing L] [BooleanRing R] [Fintype L] [Fintype R]
    (P : FolkmanNativeFinitePairing L R) :
    Nonempty (folkmanProductBundle P ↪[folkmanLanguage] M) := by
  have hP := folkmanProductBundle_mem P
  rw [← hM.age] at hP
  exact hP.2

/-- An embedding of a finite native source into the encoded limit extends
across every finite native pairing-preserving embedding of that source. -/
theorem folkmanFirstOrderLimit_nativeExtension
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M)
    {L R L' R' : Type} [BooleanRing L] [BooleanRing R] [Fintype L] [Fintype R]
    [BooleanRing L'] [BooleanRing R'] [Fintype L'] [Fintype R']
    (P : FolkmanNativeFinitePairing L R) (Q : FolkmanNativeFinitePairing L' R')
    (f : folkmanProductBundle P ↪[folkmanLanguage] M)
    (g : FolkmanNativePairingEmbedding P Q) :
    ∃ e : folkmanProductBundle Q ↪[folkmanLanguage] M,
      f = e.comp (show folkmanProductBundle P ↪[folkmanLanguage] folkmanProductBundle Q from
        folkmanNativePairingEmbeddingEquiv P Q g) := by
  have hQ := folkmanFirstOrderLimit_nativeEmbeds M hM Q
  letI : Finite (folkmanProductBundle P) := by
    change Finite (L × R)
    infer_instance
  let hPQ : folkmanProductBundle P ↪[folkmanLanguage] folkmanProductBundle Q :=
    folkmanNativePairingEmbeddingEquiv P Q g
  exact hM.ultrahomogeneous.extend_embedding Language.Structure.FG.of_finite f hPQ (h := hQ)

end SuccessorTree.NonPrecompact
