import BANANA.NonPrecompact.FolkmanNativePairingTransport

/-!
# Finite Folkman--BANANA pairings and hereditary restriction

A finite Folkman object consists of two finite Boolean rings and an
F₂-valued pairing additive in each coordinate. This module packages
the pairing hypotheses independently of the particular atom-grid
amalgamation construction.

Pulling a pairing back along two non-unital ring homomorphisms again
gives an additive pairing, even when the maps are not injective.
In particular, this provides the hereditary restriction needed for
the class of finite Folkman objects.

For fixed finite carrier rings only finitely many such pairings exist.
The global countability of isomorphism types, and joint embedding,
are separate from that fixed-carrier observation.
-/

namespace SuccessorTree.NonPrecompact

/-- A bilinear F₂-pairing on the additive groups of two Boolean rings.
The ring unit is not part of the language of embeddings. -/
structure FolkmanNativeFinitePairing (L R : Type*)
    [BooleanRing L] [BooleanRing R] where
  pairing : L → R → F2
  add_left : ∀ x x' y,
    pairing (x + x') y = pairing x y + pairing x' y
  add_right : ∀ x y y',
    pairing x (y + y') = pairing x y + pairing x y'

namespace FolkmanNativeFinitePairing

variable {L R : Type*}
variable [BooleanRing L] [BooleanRing R]

/-- Restriction of an admissible pairing along a pair of
non-unital Boolean-ring homomorphisms is again admissible. -/
def pullback
    {AL AR : Type*}
    [BooleanRing AL] [BooleanRing AR]
    (P : FolkmanNativeFinitePairing L R)
    (fL : AL →ₙ+* L) (fR : AR →ₙ+* R) :
    FolkmanNativeFinitePairing AL AR where
  pairing := fun a r => P.pairing (fL a) (fR r)
  add_left := by
    intro x x' y
    change P.pairing (fL (x + x')) (fR y) =
      P.pairing (fL x) (fR y) + P.pairing (fL x') (fR y)
    rw [map_add]
    exact P.add_left (fL x) (fL x') (fR y)
  add_right := by
    intro x y y'
    change P.pairing (fL x) (fR (y + y')) =
      P.pairing (fL x) (fR y) + P.pairing (fL x) (fR y')
    rw [map_add]
    exact P.add_right (fL x) (fR y) (fR y')

/-- The pulled-back pairing is exactly the old pairing evaluated
after the two non-unital homomorphisms. -/
@[simp] theorem pullback_pairing
    {AL AR : Type*}
    [BooleanRing AL] [BooleanRing AR]
    (P : FolkmanNativeFinitePairing L R)
    (fL : AL →ₙ+* L) (fR : AR →ₙ+* R)
    (a : AL) (r : AR) :
    (P.pullback fL fR).pairing a r =
      P.pairing (fL a) (fR r) := rfl

/-- Pairings on fixed carrier rings are determined by their values. -/
@[ext] theorem ext
    (P Q : FolkmanNativeFinitePairing L R)
    (h : P.pairing = Q.pairing) : P = Q := by
  cases P with
  | mk p hpl hpr =>
    cases Q with
    | mk q hql hqr =>
      change p = q at h
      cases h
      rfl

/-- On a fixed pair of finite Boolean-ring carriers there are
only finitely many possible bilinear F₂-valued pairings. -/
theorem finite_for_fixed_carriers [Fintype L] [Fintype R] :
    Finite (FolkmanNativeFinitePairing L R) := by
  classical
  let encode : FolkmanNativeFinitePairing L R → (L → R → F2) :=
    fun P => P.pairing
  have hinj : Function.Injective encode := by
    intro P Q h
    exact ext P Q h
  exact Finite.of_injective encode hinj

end FolkmanNativeFinitePairing
end SuccessorTree.NonPrecompact
