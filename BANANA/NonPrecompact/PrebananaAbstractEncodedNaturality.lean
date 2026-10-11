import BANANA.NonPrecompact.PrebananaAbstractEncodedEmbeddings
import BANANA.NonPrecompact.PrebananaAbstractCodeParity

/-!
# Naturality on Boolean elements of arbitrary encoded embeddings

The existing abstract embedding theorem provides a surjective
partition of target atoms and a genuine marked embedding between
the Fin-indexed atom codes. This module verifies the induced maps
on *all* Boolean elements coincide, rather than merely recording
the partition of individual atoms.

This is the key commuting-square interface for transporting
the finite powerset strong-amalgamation theorem.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Whenever a coded embedding is induced by the abstract target
atom partition, applying the embedding to the source element code
agrees exactly with coding its image in the abstract Boolean algebra. -/
theorem prebananaEncodedBooleanMap_naturality
    (α β : Type*)
    [BooleanAlgebra α] [Fintype α] [Nontrivial α]
    [BooleanAlgebra β] [Fintype β] [Nontrivial β]
    (μA : α → F2) (μB : β → F2)
    (hzeroA : μA ⊥ = 0)
    (htopA : μA ⊤ = 0)
    (haddA : ∀ x y : α, x ⊓ y = ⊥ →
      μA (x ⊔ y) = μA x + μA y)
    (hzeroB : μB ⊥ = 0)
    (htopB : μB ⊤ = 0)
    (haddB : ∀ x y : β, x ⊓ y = ⊥ →
      μB (x ⊔ y) = μB x + μB y)
    (φ : α → β)
    (f : PrebananaAtomEmbedding
      (prebananaAbstractAtomCode α μA hzeroA htopA haddA)
      (prebananaAbstractAtomCode β μB hzeroB htopB haddB))
    (part : PrebananaAbstractAtoms β → PrebananaAbstractAtoms α)
    (hpart : ∀ j : Fin (Fintype.card (PrebananaAbstractAtoms β)),
      f.part j =
        prebananaReindexedPart
          (prebananaAbstractAtomIndex α)
          (prebananaAbstractAtomIndex β) part j)
    (hpow : ∀ s : Finset (PrebananaAbstractAtoms α),
      prebananaAbstractPowersetMap φ s =
        Finset.univ.filter (fun b => part b ∈ s))
    (x : α) :
    prebananaBooleanMap f (prebananaAbstractBooleanCode α x) =
      prebananaAbstractBooleanCode β (φ x) := by
  classical
  let eA := prebananaAbstractAtomIndex α
  let eB := prebananaAbstractAtomIndex β
  let aiso := prebananaFiniteBooleanAtomFinsetOrderIso α
  let biso := prebananaFiniteBooleanAtomFinsetOrderIso β
  let S := prebananaAbstractBooleanCode α x
  have hSource : S.image eA = aiso x := by
    change ((aiso x).image eA.symm).image eA = aiso x
    simp [Finset.image_image]
  have hTarget :
      (prebananaAbstractBooleanCode β (φ x)).image eB =
      biso (φ x) := by
    change ((biso (φ x)).image eB.symm).image eB = biso (φ x)
    simp [Finset.image_image]
  have hAbstract :
      prebananaAbstractPowersetMap φ (aiso x) = biso (φ x) := by
    change biso (φ (aiso.symm (aiso x))) = biso (φ x)
    rw [aiso.symm_apply_apply]
  have hFinite :
      prebananaBooleanMap f S =
        (Finset.univ :
          Finset (Fin (Fintype.card (PrebananaAbstractAtoms β)))).filter
          (fun j => prebananaReindexedPart eA eB part j ∈ S) := by
    classical
    -- The original filter uses the canonical finite-set membership
    -- decision procedure. Pin the same DecidablePred instance in the
    -- proof, rather than allowing Classical.propDecidable to be
    -- synthesised when applying the filter-membership lemma.
    letI : DecidablePred
        (fun j : Fin (Fintype.card (PrebananaAbstractAtoms β)) =>
          prebananaReindexedPart eA eB part j ∈ S) :=
      fun j => Finset.decidableMem (prebananaReindexedPart eA eB part j) S
    -- Unfold the concrete finite atom-count projection in the embedding
    -- type, avoiding semireducible index mismatch in membership rewriting.
    dsimp only [prebananaAbstractAtomCode] at f
    -- Work extensionally: the two filters have extensionally equal
    -- membership predicates, even when their DecidablePred instances
    -- are not definitionally the same.
    ext j
    simp only [prebananaBooleanMap, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hpart j]
    -- Use the defining membership characterisation directly. This
    -- avoids asking simp to elaborate the two semireducible Fin
    -- index types under a DecidablePred instance.
    constructor
    · intro hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    · intro hj
      exact (Finset.mem_filter.mp hj).2
  have hImage :
      (prebananaBooleanMap f S).image eB =
      (prebananaAbstractBooleanCode β (φ x)).image eB := by
    calc
      (prebananaBooleanMap f S).image eB =
        ((Finset.univ :
          Finset (Fin (Fintype.card (PrebananaAbstractAtoms β)))).filter
            (fun j => prebananaReindexedPart eA eB part j ∈ S)).image eB := by
          rw [hFinite]
      _ = (Finset.univ : Finset (PrebananaAbstractAtoms β)).filter
          (fun b => part b ∈ S.image eA) :=
        prebananaReindexedBooleanMap_naturality eA eB part S
      _ = prebananaAbstractPowersetMap φ (aiso x) := by
        rw [hSource]
        exact (hpow (aiso x)).symm
      _ = biso (φ x) := hAbstract
      _ = (prebananaAbstractBooleanCode β (φ x)).image eB :=
        hTarget.symm
  change prebananaBooleanMap f S =
    prebananaAbstractBooleanCode β (φ x)
  exact (Finset.image_injective eB.injective) hImage

/-- Every genuine abstract parity-preserving embedding has a
finite coded marked embedding with exact Boolean-element naturality. -/
theorem prebananaAbstractEmbedding_exists_encodedBooleanMap
    (α β : Type*)
    [BooleanAlgebra α] [Fintype α] [Nontrivial α]
    [BooleanAlgebra β] [Fintype β] [Nontrivial β]
    (μA : α → F2) (μB : β → F2)
    (hzeroA : μA ⊥ = 0)
    (htopA : μA ⊤ = 0)
    (haddA : ∀ x y : α, x ⊓ y = ⊥ →
      μA (x ⊔ y) = μA x + μA y)
    (hzeroB : μB ⊥ = 0)
    (htopB : μB ⊤ = 0)
    (haddB : ∀ x y : β, x ⊓ y = ⊥ →
      μB (x ⊔ y) = μB x + μB y)
    (φ : α → β)
    (hinj : Function.Injective φ)
    (hbot : φ ⊥ = ⊥)
    (htop : φ ⊤ = ⊤)
    (hsup : ∀ x y : α, φ (x ⊔ y) = φ x ⊔ φ y)
    (hinf : ∀ x y : α, φ (x ⊓ y) = φ x ⊓ φ y)
    (hmark : ∀ x : α, μB (φ x) = μA x) :
    ∃ f : PrebananaAtomEmbedding
      (prebananaAbstractAtomCode α μA hzeroA htopA haddA)
      (prebananaAbstractAtomCode β μB hzeroB htopB haddB),
      ∀ x : α,
        prebananaBooleanMap f (prebananaAbstractBooleanCode α x) =
          prebananaAbstractBooleanCode β (φ x) := by
  obtain ⟨f, part, _, hpart, hpow⟩ :=
    prebananaAbstractEmbedding_exists_encodedAtomEmbedding
      α β μA μB hzeroA htopA haddA hzeroB htopB haddB
      φ hinj hbot htop hsup hinf hmark
  refine ⟨f, ?_⟩
  intro x
  exact prebananaEncodedBooleanMap_naturality
    α β μA μB hzeroA htopA haddA hzeroB htopB haddB
    φ f part hpart hpow x

end SuccessorTree.NonPrecompact
