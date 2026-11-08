import BANANA.NonPrecompact.FolkmanNativeFinitePairingClass

/-!
# Embeddings of native Folkman pairings

The two sorts are Boolean rings equipped with a pairing additive in each
coordinate. Morphisms preserve zero, addition, multiplication and the
pairing; they need not preserve the multiplicative unit. This is an
original-language interface, not a replacement by linear maps.

The identity and composition proofs do not require finite carriers.
Consequently the finite subcategory has the expected morphisms and is
closed under composition, including in the presence of zero rings.
-/

namespace SuccessorTree.NonPrecompact

/-- An embedding of the original two-sorted, non-unital Folkman language. -/
structure FolkmanNativePairingEmbedding
    {AL AR BL BR : Type*}
    [BooleanRing AL] [BooleanRing AR]
    [BooleanRing BL] [BooleanRing BR]
    (P : FolkmanNativeFinitePairing AL AR)
    (Q : FolkmanNativeFinitePairing BL BR) where
  left : AL →ₙ+* BL
  right : AR →ₙ+* BR
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  preserves_pairing : ∀ x y, Q.pairing (left x) (right y) = P.pairing x y

namespace FolkmanNativePairingEmbedding

variable {AL AR BL BR CL CR : Type*}
variable [BooleanRing AL] [BooleanRing AR]
variable [BooleanRing BL] [BooleanRing BR]
variable [BooleanRing CL] [BooleanRing CR]
variable {P : FolkmanNativeFinitePairing AL AR}
variable {Q : FolkmanNativeFinitePairing BL BR}
variable {R : FolkmanNativeFinitePairing CL CR}

/-- The identity preserves the original language, without adding a top symbol. -/
def id (P : FolkmanNativeFinitePairing AL AR) :
    FolkmanNativePairingEmbedding P P where
  left := NonUnitalRingHom.id AL
  right := NonUnitalRingHom.id AR
  left_injective := fun _ _ h => h
  right_injective := fun _ _ h => h
  preserves_pairing := fun _ _ => rfl

/-- Composition preserves the pairing and remains non-unital. -/
def comp (f : FolkmanNativePairingEmbedding P Q)
    (g : FolkmanNativePairingEmbedding Q R) :
    FolkmanNativePairingEmbedding P R where
  left := g.left.comp f.left
  right := g.right.comp f.right
  left_injective := g.left_injective.comp f.left_injective
  right_injective := g.right_injective.comp f.right_injective
  preserves_pairing := by
    intro x y
    change R.pairing (g.left (f.left x)) (g.right (f.right y)) =
      P.pairing x y
    rw [g.preserves_pairing, f.preserves_pairing]

end FolkmanNativePairingEmbedding
end SuccessorTree.NonPrecompact
