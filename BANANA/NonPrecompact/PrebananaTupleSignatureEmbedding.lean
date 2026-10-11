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

end SuccessorTree.NonPrecompact
