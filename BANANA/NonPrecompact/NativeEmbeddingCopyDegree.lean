import BANANA.NonPrecompact.FirstOrderEmbeddingCopyDegree
import BANANA.NonPrecompact.BananaNativeCopySystem
import BANANA.NonPrecompact.BananaEmbeddingDegree
import BANANA.NonPrecompact.SymplecticCopySystem

/-!
# Embedding fibres for native BANANA and finite alternating spaces

Native BANANA and alternating-space embeddings satisfy the same
range factorisation rules as first-order embeddings.
-/

namespace SuccessorTree.NonPrecompact

open Function Module

private theorem bananaEmbedding_ext {A B : BananaFiniteCopyObject}
    {f g : BananaMatrixEmbedding A.matrix B.matrix}
    (left : ∀ x, f.left x = g.left x) (right : ∀ y, f.right y = g.right y) : f = g := by
  have hleft := LinearMap.ext left
  have hright := LinearMap.ext right
  cases f
  cases g
  cases hleft
  cases hright
  rfl

private theorem banana_range_le_of_image_univ_le
    {l n : ℕ} (f g : (Fin l → F2) →ₗ[F2] (Fin n → F2))
    (h : Finset.univ.image f ⊆ Finset.univ.image g) :
    LinearMap.range f ≤ LinearMap.range g := by
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp (h (Finset.mem_image_of_mem f (Finset.mem_univ x)))
  exact ⟨y, hy⟩

private theorem banana_image_univ_eq {n : ℕ} (f : (Fin n → F2) →ₗ[F2] (Fin n → F2))
    (hf : Injective f) : Finset.univ.image f = Finset.univ := by
  refine Finset.eq_univ_of_forall (fun x => ?_)
  obtain ⟨y, rfl⟩ := Finite.surjective_of_injective hf x
  exact Finset.mem_image_of_mem f (Finset.mem_univ y)

/-- An embedding onto a native BANANA copy is determined by an
automorphism of its source relative to any fixed embedding onto it. -/
noncomputable def bananaUniformEmbeddingFibres (A : BananaFiniteCopyObject) :
    bananaCopySystem.UniformEmbeddingFibres A
      (Nat.card (bananaCopySystem.ReductAutomorphism A)) := by
  letI : Finite (bananaCopySystem.Emb A A) := Finite.of_injective
    (fun f : BananaMatrixEmbedding A.matrix A.matrix =>
      ((f.left : (Fin A.leftDim → F2) → (Fin A.leftDim → F2)),
        (f.right : (Fin A.rightDim → F2) → (Fin A.rightDim → F2))))
    (fun _ _ h => bananaEmbedding_ext (A := A) (B := A) (congrFun (congrArg Prod.fst h))
      (congrFun (congrArg Prod.snd h)))
  apply FiniteCopySystem.UniformEmbeddingFibres.of_factorisation
  · intro B g f₁ f₂ h
    exact bananaEmbedding_ext (A := A) (B := A)
      (fun x => g.left_injective (congrArg (fun e : bananaCopySystem.Emb A B => e.left x) h))
      (fun y => g.right_injective (congrArg (fun e : bananaCopySystem.Emb A B => e.right y) h))
  · intro B f g h
    exact f.exists_factor_of_range_le g
      (banana_range_le_of_image_univ_le f.left g.left
        (congrArg (fun p : bananaCopySystem.Copy A B => p.val.1) h).subset)
      (banana_range_le_of_image_univ_le f.right g.right
        (congrArg (fun p : bananaCopySystem.Copy A B => p.val.2) h).subset)
  · intro f
    apply Subtype.ext
    apply Prod.ext
    · change Finset.univ.image f.left = Finset.univ.image (id : (Fin A.leftDim → F2) → _)
      rw [banana_image_univ_eq f.left f.left_injective, Finset.image_id]
    · change Finset.univ.image f.right = Finset.univ.image (id : (Fin A.rightDim → F2) → _)
      rw [banana_image_univ_eq f.right f.right_injective, Finset.image_id]

/-- The existing native embedding-degree predicate uses the same colour
bound as the shared copy-system interface. -/
theorem bananaCopySystem_embeddingRamseyDegreeLE_iff (A : BananaFiniteCopyObject) (t : ℕ) :
    bananaCopySystem.EmbeddingRamseyDegreeLE A t ↔ A.matrix.embeddingRamseyDegreeLE t := by
  constructor
  · intro h lB rB B r hr
    obtain ⟨C, hC⟩ := h ⟨lB, rB, B⟩ r hr
    refine ⟨C.leftDim, C.rightDim, C.matrix, fun c => ?_⟩
    obtain ⟨f, hf⟩ := hC c
    refine ⟨f, FiniteCopySystem.embeddingColoursInside (S := bananaCopySystem) c f, hf,
      fun e => ?_⟩
    exact (FiniteCopySystem.mem_embeddingColoursInside (S := bananaCopySystem) c f _).mpr
      ⟨e, rfl⟩
  · intro h B r hr
    obtain ⟨lC, rC, C, hC⟩ := h B.leftDim B.rightDim B.matrix r hr
    refine ⟨⟨lC, rC, C⟩, fun c => ?_⟩
    obtain ⟨f, colours, hc, hcolours⟩ := hC c
    refine ⟨f, (Finset.card_le_card ?_).trans hc⟩
    intro _ hy
    obtain ⟨e, rfl⟩ := (FiniteCopySystem.mem_embeddingColoursInside
      (S := bananaCopySystem) (A := A) (B := B) (C := ⟨lC, rC, C⟩) c f _).mp hy
    exact hcolours e

/-- The exact embedding-to-copy comparison on the native BANANA degree
predicates. -/
theorem bananaEmbeddingRamseyDegreeLE_iff_copyRamseyDegreeLE_div
    (A : BananaFiniteCopyObject) (t : ℕ) :
    A.matrix.embeddingRamseyDegreeLE t ↔ A.matrix.copyRamseyDegreeLE
      (t / Nat.card (bananaCopySystem.ReductAutomorphism A)) := by
  rw [← bananaCopySystem_embeddingRamseyDegreeLE_iff A t,
    (bananaUniformEmbeddingFibres A).embeddingRamseyDegreeLE_iff_copyRamseyDegreeLE_div,
    bananaCopySystem_copyRamseyDegreeLE_iff A]

/-- Transfer the native BANANA copy-degree classification to embeddings.
A structure with a zero side has embedding degree
equal to the number of its automorphisms, and otherwise its degree
has no finite bound. -/
theorem bananaEmbeddingRamseyDegree_classification_of_copy
    (A : BananaFiniteCopyObject) (t : ℕ)
    (hcopy :
      ((A.rightDim = 0 ∨ A.leftDim = 0) →
        A.matrix.copyRamseyDegreeLE 1 ∧ ¬ A.matrix.copyRamseyDegreeLE 0) ∧
      ((0 < A.leftDim ∧ 0 < A.rightDim) →
        ∀ d : ℕ, ¬ A.matrix.copyRamseyDegreeLE d)) :
    A.matrix.embeddingRamseyDegreeLE t ↔
      (A.rightDim = 0 ∨ A.leftDim = 0) ∧
        Nat.card (bananaCopySystem.ReductAutomorphism A) ≤ t := by
  rw [bananaEmbeddingRamseyDegreeLE_iff_copyRamseyDegreeLE_div]
  set m := Nat.card (bananaCopySystem.ReductAutomorphism A)
  have hm : 0 < m := (bananaUniformEmbeddingFibres A).size_pos
  constructor
  · intro h
    have hside : A.rightDim = 0 ∨ A.leftDim = 0 := by
      by_contra hn
      simp only [not_or] at hn
      exact (hcopy.2
        ⟨Nat.pos_of_ne_zero hn.2, Nat.pos_of_ne_zero hn.1⟩) _ h
    have hpos : 1 ≤ t / m := by
      by_contra hn
      rw [Nat.eq_zero_of_not_pos hn] at h
      exact (hcopy.1 hside).2 h
    exact ⟨hside, by simpa using (Nat.le_div_iff_mul_le hm).mp hpos⟩
  · rintro ⟨hside, hcard⟩ lB rB B r hr
    have hpos : 1 ≤ t / m := (Nat.le_div_iff_mul_le hm).mpr (by simpa using hcard)
    obtain ⟨lC, rC, C, hC⟩ :=
      (hcopy.1 hside).1 lB rB B r hr
    exact ⟨lC, rC, C, fun c => by
      obtain ⟨f, colours, hc, hcolours⟩ := hC c
      exact ⟨f, colours, hc.trans hpos, hcolours⟩⟩

namespace FiniteAlternatingSpace

/-- Range fibres for the ordinary linear isometric embeddings of
finite alternating spaces. -/
noncomputable def uniformEmbeddingFibres (A : FiniteAlternatingSpace) :
    copySystem.UniformEmbeddingFibres A (Nat.card (copySystem.ReductAutomorphism A)) := by
  letI : Finite A.carrier := Module.finite_of_finite F2
  letI : Finite (copySystem.Emb A A) := Finite.of_injective
    (fun f : Embedding A A => (f.linear : A.carrier → A.carrier))
    (fun _ _ h => Embedding.ext (congrFun h))
  apply FiniteCopySystem.UniformEmbeddingFibres.of_factorisation
  · intro B g f₁ f₂ h
    exact Embedding.ext fun x =>
      g.injective (congrArg (fun e : Embedding A B => e.linear x) h)
  · intro B f g h
    exact f.exists_factor g (congrArg (fun p : Copy A B => p.val) h).le
  · intro f
    apply Subtype.ext
    change LinearMap.range f.linear = LinearMap.range (LinearMap.id : A.carrier →ₗ[F2] A.carrier)
    rw [LinearMap.range_eq_top.mpr (Finite.surjective_of_injective f.injective),
      LinearMap.range_id]

/-- The zero-dimensional space has only the identity automorphism. -/
theorem card_reductAutomorphism_of_finrank_zero (A : FiniteAlternatingSpace)
    (hA : finrank F2 A.carrier = 0) :
    Nat.card (copySystem.ReductAutomorphism A) = 1 := by
  let : Subsingleton A.carrier := (Module.finrank_eq_zero_iff_of_free F2 A.carrier).mp hA
  let : Unique (copySystem.ReductAutomorphism A) := {
    default := FiniteCopySystem.ReductAutomorphism.refl (S := copySystem) A
    uniq := fun f => by
      have h : f.hom = copySystem.idEmb A := Embedding.ext fun _ => Subsingleton.elim _ _
      have i : f.inv = copySystem.idEmb A := Embedding.ext fun _ => Subsingleton.elim _ _
      exact FiniteCopySystem.ReductAutomorphism.ext
        (g := FiniteCopySystem.ReductAutomorphism.refl (S := copySystem) A) h i }
  simp

end FiniteAlternatingSpace

end SuccessorTree.NonPrecompact
