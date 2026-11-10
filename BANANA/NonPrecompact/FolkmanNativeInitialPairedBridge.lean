import BANANA.NonPrecompact.FolkmanFinitePairedBridgePreorder
import BANANA.NonPrecompact.FolkmanNativeFiniteCodeRealisation

/-!
# A finite paired bridge from two faithful native embeddings

A finite Folkman object has an exact atom-code ring isomorphism in
the original non-unital language (Track B). If it embeds twice into
the same original two-sorted pairing and both embeddings preserve
every original pairing value, its atom code is a finite paired bridge.

This construction requires no ambient multiplicative identity.
Both copies use the SAME finite pairing matrix and both maps are
the specified native homomorphisms, not abstract unrelated owners.

The result is a building block for an initial bridge representing
any isomorphism of two finite generated substructures. The global
extension property is not assumed here.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- Any two faithful representations of one finite native Folkman
object in an ambient non-unital pairing produce a finite paired
bridge. The native code equivalence is supplied explicitly so that
the named elements can subsequently be represented in this code. -/
noncomputable def folkmanFinitePairedBridge_of_nativeIso
    {AL AR L R : Type*}
    [BooleanRing AL] [Fintype AL]
    [BooleanRing AR] [Fintype AR]
    [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2)
    (P : FolkmanNativeFinitePairing AL AR)
    (I : FolkmanNativeFinitePairingIso P
      (folkmanNativeCodeRealisation (folkmanNativeFinCode P.pairing)))
    (fL : AL →ₙ+* L) (fR : AR →ₙ+* R)
    (gL : AL →ₙ+* L) (gR : AR →ₙ+* R)
    (hfL : Function.Injective fL) (hfR : Function.Injective fR)
    (hgL : Function.Injective gL) (hgR : Function.Injective gR)
    (hF : ∀ x y, β (fL x) (fR y) = P.pairing x y)
    (hG : ∀ x y, β (gL x) (gR y) = P.pairing x y) :
    FolkmanFinitePairedBridge L R β where
  source := {
    atom := folkmanNativeFinCode P.pairing
    left := fL.comp (I.left.symm : _ →ₙ+* AL)
    right := fR.comp (I.right.symm : _ →ₙ+* AR)
    left_injective := by
      intro a b hab
      apply I.left.symm.injective
      apply hfL
      exact hab
    right_injective := by
      intro a b hab
      apply I.right.symm.injective
      apply hfR
      exact hab
    preserves_pairing := by
      intro s t
      change β (fL (I.left.symm (toBoolRing s)))
          (fR (I.right.symm (toBoolRing t))) =
        ∑ i ∈ s, ∑ j ∈ t,
          (folkmanNativeFinCode P.pairing).edge i j
      calc
        β (fL (I.left.symm (toBoolRing s)))
            (fR (I.right.symm (toBoolRing t))) =
          P.pairing (I.left.symm (toBoolRing s))
            (I.right.symm (toBoolRing t)) :=
          hF _ _
        _ = (folkmanNativeCodeRealisation
            (folkmanNativeFinCode P.pairing)).pairing
              (toBoolRing s) (toBoolRing t) := by
          have h := I.preserves_pairing
            (I.left.symm (toBoolRing s))
            (I.right.symm (toBoolRing t))
          simpa only [I.left.apply_symm_apply,
            I.right.apply_symm_apply] using h.symm
        _ = ∑ i ∈ s, ∑ j ∈ t,
              (folkmanNativeFinCode P.pairing).edge i j := rfl
  }
  targetLeft := gL.comp (I.left.symm : _ →ₙ+* AL)
  targetRight := gR.comp (I.right.symm : _ →ₙ+* AR)
  targetLeft_injective := by
    intro a b hab
    apply I.left.symm.injective
    apply hgL
    exact hab
  targetRight_injective := by
    intro a b hab
    apply I.right.symm.injective
    apply hgR
    exact hab
  target_pairing := by
    intro s t
    change β (gL (I.left.symm (toBoolRing s)))
        (gR (I.right.symm (toBoolRing t))) =
      ∑ i ∈ s, ∑ j ∈ t,
        (folkmanNativeFinCode P.pairing).edge i j
    calc
      β (gL (I.left.symm (toBoolRing s)))
          (gR (I.right.symm (toBoolRing t))) =
        P.pairing (I.left.symm (toBoolRing s))
          (I.right.symm (toBoolRing t)) :=
        hG _ _
      _ = (folkmanNativeCodeRealisation
          (folkmanNativeFinCode P.pairing)).pairing
            (toBoolRing s) (toBoolRing t) := by
        have h := I.preserves_pairing
          (I.left.symm (toBoolRing s))
          (I.right.symm (toBoolRing t))
        simpa only [I.left.apply_symm_apply,
          I.right.apply_symm_apply] using h.symm
      _ = ∑ i ∈ s, ∑ j ∈ t,
            (folkmanNativeFinCode P.pairing).edge i j := rfl

/-- The source of the paired bridge applies the originally specified
left embedding to the finite native ring element named by the code. -/
theorem folkmanFinitePairedBridge_of_nativeIso_sourceLeft
    {AL AR L R : Type*}
    [BooleanRing AL] [Fintype AL] [BooleanRing AR] [Fintype AR]
    [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2)
    (P : FolkmanNativeFinitePairing AL AR)
    (I : FolkmanNativeFinitePairingIso P
      (folkmanNativeCodeRealisation (folkmanNativeFinCode P.pairing)))
    (fL : AL →ₙ+* L) (fR : AR →ₙ+* R)
    (gL : AL →ₙ+* L) (gR : AR →ₙ+* R)
    (hfL : Function.Injective fL) (hfR : Function.Injective fR)
    (hgL : Function.Injective gL) (hgR : Function.Injective gR)
    (hF : ∀ x y, β (fL x) (fR y) = P.pairing x y)
    (hG : ∀ x y, β (gL x) (gR y) = P.pairing x y)
    (x : AL) :
    (folkmanFinitePairedBridge_of_nativeIso
        β P I fL fR gL gR hfL hfR hgL hgR hF hG).source.left
        (I.left x) = fL x := by
  change fL (I.left.symm (I.left x)) = fL x
  rw [I.left.symm_apply_apply]

/-- The second left copy realises the target embedding, again on
the *same* finite code for the entire native source ring. -/
theorem folkmanFinitePairedBridge_of_nativeIso_targetLeft
    {AL AR L R : Type*}
    [BooleanRing AL] [Fintype AL] [BooleanRing AR] [Fintype AR]
    [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2)
    (P : FolkmanNativeFinitePairing AL AR)
    (I : FolkmanNativeFinitePairingIso P
      (folkmanNativeCodeRealisation (folkmanNativeFinCode P.pairing)))
    (fL : AL →ₙ+* L) (fR : AR →ₙ+* R)
    (gL : AL →ₙ+* L) (gR : AR →ₙ+* R)
    (hfL : Function.Injective fL) (hfR : Function.Injective fR)
    (hgL : Function.Injective gL) (hgR : Function.Injective gR)
    (hF : ∀ x y, β (fL x) (fR y) = P.pairing x y)
    (hG : ∀ x y, β (gL x) (gR y) = P.pairing x y)
    (x : AL) :
    (folkmanFinitePairedBridge_of_nativeIso
        β P I fL fR gL gR hfL hfR hgL hgR hF hG).targetLeft
        (I.left x) = gL x := by
  change gL (I.left.symm (I.left x)) = gL x
  rw [I.left.symm_apply_apply]

/-- The right-sort source and target maps have the analogous
exact interpretation on every original finite native element. -/
theorem folkmanFinitePairedBridge_of_nativeIso_sourceRight
    {AL AR L R : Type*}
    [BooleanRing AL] [Fintype AL] [BooleanRing AR] [Fintype AR]
    [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2)
    (P : FolkmanNativeFinitePairing AL AR)
    (I : FolkmanNativeFinitePairingIso P
      (folkmanNativeCodeRealisation (folkmanNativeFinCode P.pairing)))
    (fL : AL →ₙ+* L) (fR : AR →ₙ+* R)
    (gL : AL →ₙ+* L) (gR : AR →ₙ+* R)
    (hfL : Function.Injective fL) (hfR : Function.Injective fR)
    (hgL : Function.Injective gL) (hgR : Function.Injective gR)
    (hF : ∀ x y, β (fL x) (fR y) = P.pairing x y)
    (hG : ∀ x y, β (gL x) (gR y) = P.pairing x y)
    (x : AR) :
    (folkmanFinitePairedBridge_of_nativeIso
        β P I fL fR gL gR hfL hfR hgL hgR hF hG).source.right
        (I.right x) = fR x := by
  change fR (I.right.symm (I.right x)) = fR x
  rw [I.right.symm_apply_apply]

theorem folkmanFinitePairedBridge_of_nativeIso_targetRight
    {AL AR L R : Type*}
    [BooleanRing AL] [Fintype AL] [BooleanRing AR] [Fintype AR]
    [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2)
    (P : FolkmanNativeFinitePairing AL AR)
    (I : FolkmanNativeFinitePairingIso P
      (folkmanNativeCodeRealisation (folkmanNativeFinCode P.pairing)))
    (fL : AL →ₙ+* L) (fR : AR →ₙ+* R)
    (gL : AL →ₙ+* L) (gR : AR →ₙ+* R)
    (hfL : Function.Injective fL) (hfR : Function.Injective fR)
    (hgL : Function.Injective gL) (hgR : Function.Injective gR)
    (hF : ∀ x y, β (fL x) (fR y) = P.pairing x y)
    (hG : ∀ x y, β (gL x) (gR y) = P.pairing x y)
    (x : AR) :
    (folkmanFinitePairedBridge_of_nativeIso
        β P I fL fR gL gR hfL hfR hgL hgR hF hG).targetRight
        (I.right x) = gR x := by
  change gR (I.right.symm (I.right x)) = gR x
  rw [I.right.symm_apply_apply]

end SuccessorTree.NonPrecompact
