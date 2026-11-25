import BANANA.NonPrecompact.BananaNativeCoherentEppa

/-! Sortwise linear, pairing-preserving embeddings of native BANANA structures. -/

namespace SuccessorTree.NonPrecompact.BananaNative

variable {AL AR BL BR CL CR : Type*}
  [AddCommGroup AL] [AddCommGroup AR] [Module F2 AL] [Module F2 AR]
  [AddCommGroup BL] [AddCommGroup BR] [Module F2 BL] [Module F2 BR]
  [AddCommGroup CL] [AddCommGroup CR] [Module F2 CL] [Module F2 CR]

/-- A BANANA embedding consists of two injective linear maps preserving the pairing. -/
structure PairingEmbedding (β : AL → AR → F2) (γ : BL → BR → F2) where
  left : AL →ₗ[F2] BL
  right : AR →ₗ[F2] BR
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  preserves : ∀ x y, γ (left x) (right y) = β x y

namespace PairingEmbedding

/-- The identity pairing embedding. -/
protected def refl (β : AL → AR → F2) : PairingEmbedding β β where
  left := LinearMap.id
  right := LinearMap.id
  left_injective := Function.injective_id
  right_injective := Function.injective_id
  preserves _ _ := rfl

/-- Compose two pairing embeddings. -/
def comp {α : AL → AR → F2} {β : BL → BR → F2} {γ : CL → CR → F2}
    (g : PairingEmbedding β γ) (f : PairingEmbedding α β) : PairingEmbedding α γ where
  left := g.left.comp f.left
  right := g.right.comp f.right
  left_injective := g.left_injective.comp f.left_injective
  right_injective := g.right_injective.comp f.right_injective
  preserves _ _ := (g.preserves _ _).trans (f.preserves _ _)

@[ext]
theorem ext {α : AL → AR → F2} {β : BL → BR → F2} {f g : PairingEmbedding α β}
    (hl : f.left = g.left) (hr : f.right = g.right) : f = g := by
  cases f
  cases g
  cases hl
  cases hr
  rfl

end PairingEmbedding

/-- A pairing isomorphism gives a pairing embedding. -/
def PairingEquiv.toPairingEmbedding {α : AL → AR → F2} {β : BL → BR → F2}
    (f : PairingEquiv α β) : PairingEmbedding α β where
  left := f.left.toLinearMap
  right := f.right.toLinearMap
  left_injective := f.left.injective
  right_injective := f.right.injective
  preserves := f.preserves

end SuccessorTree.NonPrecompact.BananaNative
