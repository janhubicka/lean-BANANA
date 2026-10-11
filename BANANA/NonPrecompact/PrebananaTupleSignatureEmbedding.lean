import BANANA.NonPrecompact.PrebananaTupleSignatures
import BANANA.NonPrecompact.PrebananaPowersetBridge

/-!
# Naturality of finite pre-BANANA tuple membership signatures

An atom of a finite Boolean algebra determines an `n`-bit signature
relative to an `n`-tuple. Under an atom-partition embedding, each
target atom has the signature of its source-fibre atom. Since all
source fibres are nonempty, the set of realised signatures is
unchanged.

This is a finite combinatorial interface for the orbit-classification
part of the circulation proof. It does not itself assert homogeneity
of the Fraïssé limit or classify its orbits.
-/

namespace SuccessorTree.NonPrecompact

/-- The membership signature of a target atom is that of the source
atom labelling its fibre. -/
theorem prebananaAtomSignature_booleanMap
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    {n : ℕ}
    (tuple : Fin n → Finset (Fin A.atomCount))
    (b : Fin B.atomCount) :
    prebananaAtomSignature B
      (fun i => prebananaBooleanMap f (tuple i)) b =
      prebananaAtomSignature A tuple (f.part b) := by
  classical
  funext i
  simp [prebananaAtomSignature, prebananaBooleanMap]

/-- A genuine finite atom-partition embedding preserves exactly the
realised Boolean membership signatures of every finite tuple. -/
theorem prebananaRealisedSignatures_booleanMap
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    {n : ℕ}
    (tuple : Fin n → Finset (Fin A.atomCount)) :
    prebananaRealisedSignatures B
        (fun i => prebananaBooleanMap f (tuple i)) =
      prebananaRealisedSignatures A tuple := by
  classical
  unfold prebananaRealisedSignatures
  ext pattern
  constructor
  · intro hp
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr
      ⟨f.part b, Finset.mem_univ _, ?_⟩
    rw [prebananaAtomSignature_booleanMap f tuple b] at hb
    exact hb
  · intro hp
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb⟩ := f.part_surjective a
    refine Finset.mem_image.mpr
      ⟨b, Finset.mem_univ _, ?_⟩
    rw [prebananaAtomSignature_booleanMap f tuple b, hb]
    exact ha

/-- Parities of every tuple-membership-pattern fibre are preserved
by marked Boolean embeddings, not just the realised signatures. -/
theorem prebananaSignatureMark_booleanMap
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    {n : ℕ}
    (tuple : Fin n → Finset (Fin A.atomCount))
    (pattern : Fin n → Bool) :
    prebananaSignatureMark B
      (fun i => prebananaBooleanMap f (tuple i)) pattern =
      prebananaSignatureMark A tuple pattern := by
  classical
  let support : Finset (Fin A.atomCount) :=
    Finset.univ.filter
      (fun a => prebananaAtomSignature A tuple a = pattern)
  have hSupport :
      (Finset.univ : Finset (Fin B.atomCount)).filter
        (fun b =>
          prebananaAtomSignature B
            (fun i => prebananaBooleanMap f (tuple i)) b =
          pattern) =
      prebananaBooleanMap f support := by
    ext b
    simp only [prebananaBooleanMap, support, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hsig := prebananaAtomSignature_booleanMap f tuple b
    simp only [prebananaBooleanMap] at hsig
    rw [hsig]
  change
    (∑ b ∈ (Finset.univ : Finset (Fin B.atomCount)).filter
      (fun b =>
        prebananaAtomSignature B
          (fun i => prebananaBooleanMap f (tuple i)) b = pattern),
      B.mark b) =
    ∑ a ∈ (Finset.univ : Finset (Fin A.atomCount)).filter
      (fun a => prebananaAtomSignature A tuple a = pattern), A.mark a
  rw [hSupport]
  change
    (∑ b ∈ prebananaBooleanMap f support, B.mark b) =
      ∑ a ∈ support, A.mark a
  calc
    (∑ b ∈ prebananaBooleanMap f support, B.mark b) =
        prebananaBooleanParity B (prebananaBooleanMap f support) := by
          exact (prebananaMarkedCount_cast_eq_sum B.mark
            (prebananaBooleanMap f support)).symm
    _ = prebananaBooleanParity A support :=
          prebananaBooleanMap_parity f support
    _ = ∑ a ∈ support, A.mark a :=
          prebananaMarkedCount_cast_eq_sum A.mark support

/-- The complete finite tuple profile is invariant under every
pre-BANANA marked Boolean embedding. This is a finite algebraic
statement and does not itself prove orbit classification. -/
theorem prebananaTupleProfile_booleanMap
    {A B : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding A B)
    {n : ℕ}
    (tuple : Fin n → Finset (Fin A.atomCount)) :
    prebananaTupleProfile B
        (fun i => prebananaBooleanMap f (tuple i)) =
      prebananaTupleProfile A tuple := by
  classical
  apply Prod.ext
  · exact prebananaRealisedSignatures_booleanMap f tuple
  · funext pattern
    exact prebananaSignatureMark_booleanMap f tuple pattern

end SuccessorTree.NonPrecompact
