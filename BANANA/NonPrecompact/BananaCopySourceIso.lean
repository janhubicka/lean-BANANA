import BANANA.NonPrecompact.BananaCopyFunctor

/-!
# Track E: changing the source coordinates of unlabelled BANANA copies

A copy is a pair of ambient image sets, not a chosen parametrisation.
Consequently a pairing-preserving change of bases in the source does not
change the copy type, or its action under an ambient embedding.

This module deliberately supplies the source-coordinate bridge rather than
assuming that an embedding-colouring theorem is about unlabelled copies.
It is an uncompiled development branch pending an exact-head Lean/Lake build
and transitive axiom audit. Do not import into the root until verified.
-/

namespace SuccessorTree.NonPrecompact

/-- Pairing-preserving coordinate changes between two finite BANANA
matrix presentations. The equivalences may change both dimensions
and the chosen bases, but preserve the pairing on every pair. -/
structure BananaCopySourceIso
    {l r l' r' : ℕ}
    (A : BananaMatrixStructure l r)
    (A' : BananaMatrixStructure l' r') where
  left : (Fin l → F2) ≃ₗ[F2] (Fin l' → F2)
  right : (Fin r → F2) ≃ₗ[F2] (Fin r' → F2)
  pairing_apply : ∀ x y, A'.eval (left x) (right y) = A.eval x y

namespace BananaCopySourceIso

variable {l r l' r' lB rB lC rC : ℕ}
variable {A : BananaMatrixStructure l r}
variable {A' : BananaMatrixStructure l' r'}

/-- A coordinate isomorphism is an embedding in the original language. -/
def toEmbedding (i : BananaCopySourceIso A A') :
    BananaMatrixEmbedding A A' where
  left := i.left.toLinearMap
  right := i.right.toLinearMap
  left_injective := i.left.injective
  right_injective := i.right.injective
  pairing_apply := i.pairing_apply

/-- Reverse the coordinate isomorphism. -/
def symm (i : BananaCopySourceIso A A') :
    BananaCopySourceIso A' A where
  left := i.left.symm
  right := i.right.symm
  pairing_apply := by
    intro x y
    have h := i.pairing_apply (i.left.symm x) (i.right.symm y)
    simpa using h.symm

/-- A bijection of finite indexing sets does not change the image of
a map after reparametrisation. -/
private theorem univ_image_comp_equiv
    {X Y Z : Type*} [Fintype X] [Fintype Y] [DecidableEq Z]
    (g : X ≃ Y) (h : Y → Z) :
    (Finset.univ : Finset X).image (fun x => h (g x)) =
      (Finset.univ : Finset Y).image h := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨g x, Finset.mem_univ _, hx⟩
  · intro hz
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr
      ⟨g.symm y, Finset.mem_univ _, by simpa using hy⟩

/-- Precomposing an embedding by a coordinate isomorphism changes
neither of its two image sets. -/
private theorem ranges_comp_sourceIso
    {a b a' b' c d : ℕ}
    {X : BananaMatrixStructure a b}
    {Y : BananaMatrixStructure a' b'}
    {C : BananaMatrixStructure c d}
    (e : BananaMatrixEmbedding Y C)
    (i : BananaCopySourceIso X Y) :
    ((Finset.univ : Finset (Fin a' → F2)).image e.left,
       (Finset.univ : Finset (Fin b' → F2)).image e.right) =
      ((Finset.univ : Finset (Fin a → F2)).image
          (BananaMatrixEmbedding.comp e i.toEmbedding).left,
       (Finset.univ : Finset (Fin b → F2)).image
          (BananaMatrixEmbedding.comp e i.toEmbedding).right) := by
  apply Prod.ext
  · change (Finset.univ : Finset (Fin a' → F2)).image e.left =
      (Finset.univ : Finset (Fin a → F2)).image
        (fun x => e.left (i.left x))
    exact (univ_image_comp_equiv i.left.toEquiv e.left).symm
  · change (Finset.univ : Finset (Fin b' → F2)).image e.right =
      (Finset.univ : Finset (Fin b → F2)).image
        (fun x => e.right (i.right x))
    exact (univ_image_comp_equiv i.right.toEquiv e.right).symm

/-- Precomposition by a pairing-preserving source isomorphism
does not change an unlabelled copy. In particular this works for
nonrigid sources: it is about images, not embedding parameters. -/
theorem copyRanges_precompose
    (i : BananaCopySourceIso A A')
    {C : BananaMatrixStructure lC rC}
    (e : BananaMatrixEmbedding A' C) :
    (BananaMatrixEmbedding.comp e i.toEmbedding).copyRanges =
      e.copyRanges := by
  classical
  apply Subtype.ext
  exact (ranges_comp_sourceIso e i).symm

/-- A pair of ambient ranges is an A-copy if and only if it is
an A'-copy when the two sources are isomorphic. -/
private theorem copyPredicate_iff
    (i : BananaCopySourceIso A A')
    (C : BananaMatrixStructure lC rC)
    (ranges : Finset (Fin lC → F2) × Finset (Fin rC → F2)) :
    (∃ e : BananaMatrixEmbedding A C,
       ranges.1 = Finset.univ.image e.left ∧
       ranges.2 = Finset.univ.image e.right) ↔
    (∃ e' : BananaMatrixEmbedding A' C,
       ranges.1 = Finset.univ.image e'.left ∧
       ranges.2 = Finset.univ.image e'.right) := by
  constructor
  · rintro ⟨e, hl, hr⟩
    let e' : BananaMatrixEmbedding A' C :=
      BananaMatrixEmbedding.comp e i.symm.toEmbedding
    have h := ranges_comp_sourceIso e i.symm
    refine ⟨e', ?_, ?_⟩
    · exact hl.trans (congrArg Prod.fst h)
    · exact hr.trans (congrArg Prod.snd h)
  · rintro ⟨e, hl, hr⟩
    let e' : BananaMatrixEmbedding A C :=
      BananaMatrixEmbedding.comp e i.toEmbedding
    have h := ranges_comp_sourceIso e i
    refine ⟨e', ?_, ?_⟩
    · exact hl.trans (congrArg Prod.fst h)
    · exact hr.trans (congrArg Prod.snd h)

/-- Bijection between unlabelled copies of two isomorphic sources
in an arbitrary finite ambient pairing. The bijection retains the
*same* underlying pair of image sets. -/
noncomputable def copyRangesEquiv
    (i : BananaCopySourceIso A A')
    (C : BananaMatrixStructure lC rC) :
    BananaCopyRanges A C ≃ BananaCopyRanges A' C where
  toFun := fun D => ⟨D.1, (i.copyPredicate_iff C D.1).mp D.2⟩
  invFun := fun D => ⟨D.1, (i.copyPredicate_iff C D.1).mpr D.2⟩
  left_inv := by
    intro D
    apply Subtype.ext
    rfl
  right_inv := by
    intro D
    apply Subtype.ext
    rfl

/-- Changing source coordinates commutes with embeddings of the
ambient structure, so the colour-transport argument is natural. -/
theorem copyRangesEquiv_map
    (i : BananaCopySourceIso A A')
    (B : BananaMatrixStructure lB rB)
    (C : BananaMatrixStructure lC rC)
    (D : BananaCopyRanges A B)
    (f : BananaMatrixEmbedding B C) :
    (i.copyRangesEquiv B D).map f =
      i.copyRangesEquiv C (D.map f) := by
  apply Subtype.ext
  rfl

/-- The Ramsey-degree bound is invariant under a pairing-preserving
change of source bases. No choice of a source representative affects
the number of colours on copies. -/
theorem copyRamseyDegreeLE_imp
    (i : BananaCopySourceIso A A')
    (t : ℕ)
    (h : A.copyRamseyDegreeLE t) :
    A'.copyRamseyDegreeLE t := by
  classical
  intro lB rB B numColours hpositive
  obtain ⟨lC, rC, C, hC⟩ := h lB rB B numColours hpositive
  refine ⟨lC, rC, C, ?_⟩
  intro colouring
  let sourceColour : BananaCopyRanges A C → Fin numColours :=
    fun D => colouring (i.copyRangesEquiv C D)
  obtain ⟨f, used, hcard, hused⟩ := hC sourceColour
  refine ⟨f, used, hcard, ?_⟩
  intro D'
  have hD := hused ((i.copyRangesEquiv B).symm D')
  change
    colouring (i.copyRangesEquiv C
      (((i.copyRangesEquiv B).symm D').map f)) ∈ used at hD
  have hcomm :
      i.copyRangesEquiv C
        (((i.copyRangesEquiv B).symm D').map f) = D'.map f := by
    calc
      i.copyRangesEquiv C
          (((i.copyRangesEquiv B).symm D').map f) =
        (i.copyRangesEquiv B ((i.copyRangesEquiv B).symm D')).map f :=
          (i.copyRangesEquiv_map B C
            ((i.copyRangesEquiv B).symm D') f).symm
      _ = D'.map f := by rw [Equiv.apply_symm_apply]
  rw [hcomm] at hD
  exact hD

/-- Source-coordinate invariance of the complete copy-degree predicate. -/
theorem copyRamseyDegreeLE_iff
    (i : BananaCopySourceIso A A')
    (t : ℕ) :
    A.copyRamseyDegreeLE t ↔ A'.copyRamseyDegreeLE t := by
  exact ⟨i.copyRamseyDegreeLE_imp t,
    i.symm.copyRamseyDegreeLE_imp t⟩

/-- The already formalised two-case classification transports
without loss along *any* source change of coordinates. Its cases are
indexed by the dimensions of `A`; an isomorphism preserves them. -/
theorem copyRamseyDegree_classification_transport
    (i : BananaCopySourceIso A A') :
    ((r = 0 ∨ l = 0) →
       A'.copyRamseyDegreeLE 1 ∧ ¬ A'.copyRamseyDegreeLE 0) ∧
    ((0 < l ∧ 0 < r) →
       ∀ t : ℕ, ¬ A'.copyRamseyDegreeLE t) := by
  obtain ⟨hone, hinfinite⟩ := A.copyRamseyDegree_classification
  constructor
  · intro hzero
    obtain ⟨hdegree, hnonzero⟩ := hone hzero
    constructor
    · exact (i.copyRamseyDegreeLE_iff 1).mp hdegree
    · intro hz
      exact hnonzero ((i.copyRamseyDegreeLE_iff 0).mpr hz)
  · intro hboth t ht
    exact hinfinite hboth t ((i.copyRamseyDegreeLE_iff t).mpr ht)

end BananaCopySourceIso

end SuccessorTree.NonPrecompact
