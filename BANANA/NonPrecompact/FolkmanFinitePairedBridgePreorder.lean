import BANANA.NonPrecompact.FolkmanDirectedFiniteStageAtlas

/-!
# A finite paired Folkman bridge and its extension preorder

A paired bridge consists of a finite atom-coded two-sort Folkman
structure embedded *twice* in one ambient non-unital two-sort
pairing. The source and target embeddings each reconstruct the
same finite atom matrix on all ring elements.

An extension is a pair of injective non-unital ring homomorphisms
between the finite codes, commuting with all four embeddings.
The pairing is consequently preserved without adding a separate,
potentially inconsistent, matrix-preservation assumption.

Identity and composition are proved in the original non-unital
language. We use a preorder, not a partial order: different finite
presentations may represent the same pair of finite images.

This file does not construct a Fraisse limit or an exhaustive chain.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- The source is a faithful finite atom stage. The target embeds
the very same finite code and must reconstruct its exact pairing.
Neither ambient sort is assumed to have a multiplicative identity. -/
structure FolkmanFinitePairedBridge
    (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) where
  source : FolkmanFiniteAtomStage L R β
  targetLeft :
    AsBoolRing (Finset (Fin source.atom.leftCount)) →ₙ+* L
  targetRight :
    AsBoolRing (Finset (Fin source.atom.rightCount)) →ₙ+* R
  targetLeft_injective : Function.Injective targetLeft
  targetRight_injective : Function.Injective targetRight
  target_pairing :
    ∀ (s : Finset (Fin source.atom.leftCount))
      (t : Finset (Fin source.atom.rightCount)),
      β (targetLeft (toBoolRing s))
        (targetRight (toBoolRing t)) =
        ∑ i ∈ s, ∑ j ∈ t, source.atom.edge i j

/-- A finite code embedding which commutes on *all* original
source and target elements of both ring sorts. These square
identities are stronger than an abstract equality of atom matrices. -/
structure FolkmanFinitePairedBridgeMap
    {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
    {β : L → R → F2}
    (P Q : FolkmanFinitePairedBridge L R β) where
  left : AsBoolRing (Finset (Fin P.source.atom.leftCount)) →ₙ+*
    AsBoolRing (Finset (Fin Q.source.atom.leftCount))
  right : AsBoolRing (Finset (Fin P.source.atom.rightCount)) →ₙ+*
    AsBoolRing (Finset (Fin Q.source.atom.rightCount))
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  source_left_comm : ∀ x,
    Q.source.left (left x) = P.source.left x
  target_left_comm : ∀ x,
    Q.targetLeft (left x) = P.targetLeft x
  source_right_comm : ∀ y,
    Q.source.right (right y) = P.source.right y
  target_right_comm : ∀ y,
    Q.targetRight (right y) = P.targetRight y

namespace FolkmanFinitePairedBridgeMap

variable {L R : Type*} [NonUnitalRing L] [NonUnitalRing R]
variable {β : L → R → F2}
variable {P Q T : FolkmanFinitePairedBridge L R β}

/-- Identity of a concrete finite paired bridge. -/
def id (P : FolkmanFinitePairedBridge L R β) :
    FolkmanFinitePairedBridgeMap P P where
  left := NonUnitalRingHom.id _
  right := NonUnitalRingHom.id _
  left_injective := fun _ _ h => h
  right_injective := fun _ _ h => h
  source_left_comm := fun _ => rfl
  target_left_comm := fun _ => rfl
  source_right_comm := fun _ => rfl
  target_right_comm := fun _ => rfl

/-- Composition respects all four original ambient embeddings. -/
def comp (f : FolkmanFinitePairedBridgeMap P Q)
    (g : FolkmanFinitePairedBridgeMap Q T) :
    FolkmanFinitePairedBridgeMap P T where
  left := g.left.comp f.left
  right := g.right.comp f.right
  left_injective := g.left_injective.comp f.left_injective
  right_injective := g.right_injective.comp f.right_injective
  source_left_comm := by
    intro x
    exact (g.source_left_comm (f.left x)).trans (f.source_left_comm x)
  target_left_comm := by
    intro x
    exact (g.target_left_comm (f.left x)).trans (f.target_left_comm x)
  source_right_comm := by
    intro y
    exact (g.source_right_comm (f.right y)).trans (f.source_right_comm y)
  target_right_comm := by
    intro y
    exact (g.target_right_comm (f.right y)).trans (f.target_right_comm y)

/-- The source atom matrices are compatible with any bridge extension,
as a consequence of faithful pairing reconstruction and commutation.
This is not merely equality on selected singleton generators. -/
theorem preserves_source_pairing (f : FolkmanFinitePairedBridgeMap P Q)
    (s : Finset (Fin P.source.atom.leftCount))
    (t : Finset (Fin P.source.atom.rightCount)) :
    (∑ i ∈ s, ∑ j ∈ t, P.source.atom.edge i j) =
      ∑ i ∈ ofBoolRing (f.left (toBoolRing s)),
        ∑ j ∈ ofBoolRing (f.right (toBoolRing t)),
          Q.source.atom.edge i j := by
  calc
    (∑ i ∈ s, ∑ j ∈ t, P.source.atom.edge i j) =
        β (P.source.left (toBoolRing s))
          (P.source.right (toBoolRing t)) :=
      (P.source.preserves_pairing s t).symm
    _ = β (Q.source.left (f.left (toBoolRing s)))
          (Q.source.right (f.right (toBoolRing t))) := by
      rw [f.source_left_comm, f.source_right_comm]
    _ = ∑ i ∈ ofBoolRing (f.left (toBoolRing s)),
          ∑ j ∈ ofBoolRing (f.right (toBoolRing t)),
            Q.source.atom.edge i j :=
      Q.source.preserves_pairing _ _

end FolkmanFinitePairedBridgeMap

/-- The extension relation remembers genuine finite ring maps and
their four commuting squares, rather than equality of presentations. -/
instance (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) :
    LE (FolkmanFinitePairedBridge L R β) where
  le P Q := Nonempty (FolkmanFinitePairedBridgeMap P Q)

/-- Finite paired bridge extension is a preorder. No antisymmetry
is imposed between distinct finite presentations of the same image. -/
instance (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) :
    Preorder (FolkmanFinitePairedBridge L R β) where
  le_refl P := ⟨FolkmanFinitePairedBridgeMap.id P⟩
  le_trans P Q T hPQ hQT := by
    obtain ⟨f⟩ := hPQ
    obtain ⟨g⟩ := hQT
    exact ⟨f.comp g⟩

end SuccessorTree.NonPrecompact
