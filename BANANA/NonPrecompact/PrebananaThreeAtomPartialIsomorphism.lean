import BANANA.NonPrecompact.PrebananaAbstractEppaFiniteObstruction
import BANANA.NonPrecompact.PrebananaGeneratedMarkedIsomorphism

/-!
# The actual three-atom pre-BANANA partial isomorphism

The finite EPPA obstruction alone is not sufficient: one must also
exhibit a genuine partial isomorphism of the source. Here the source
is the Boolean powerset of three unmarked atoms. The one-element
generated subalgebras of {0} and {0,1} each have four elements and
are isomorphic as marked Boolean algebras by the correspondence
sending the first generator to the second.

We prove this through the existing complete finite Boolean tuple
profiles and construct the operation- and mark-preserving generated
isomorphism; it is not a purported automorphism of the ambient
three-atom Boolean algebra.
-/

namespace SuccessorTree.NonPrecompact

/-- Both membership patterns of a single Boolean generator occur
as soon as the generator contains an atom and its complement
contains an atom. -/
theorem prebanana_oneGenerator_all_signatures
    (A : PrebananaAtomStructure)
    (s : Finset (Fin A.atomCount))
    (yes no : Fin A.atomCount)
    (hyes : yes ∈ s) (hno : no ∉ s) :
    prebananaRealisedSignatures A (fun _ : Fin 1 => s) =
      Finset.univ := by
  classical
  ext p
  simp only [Finset.mem_univ, iff_true]
  by_cases hp : p (0 : Fin 1) = true
  · change p ∈ (Finset.univ : Finset (Fin A.atomCount)).image
      (prebananaAtomSignature A (fun _ : Fin 1 => s))
    apply Finset.mem_image.mpr
    refine ⟨yes, Finset.mem_univ _, ?_⟩
    funext i
    fin_cases i
    simp [prebananaAtomSignature, hyes, hp]
  · have hf : p (0 : Fin 1) = false := by
      cases hb : p (0 : Fin 1) with
      | false => rfl
      | true => exact False.elim (hp hb)
    change p ∈ (Finset.univ : Finset (Fin A.atomCount)).image
      (prebananaAtomSignature A (fun _ : Fin 1 => s))
    apply Finset.mem_image.mpr
    refine ⟨no, Finset.mem_univ _, ?_⟩
    funext i
    fin_cases i
    simp [prebananaAtomSignature, hno, hf]

/-- For the three-atom all-unmarked pre-BANANA source, the
one-element tuples {0} and {0,1} have identical complete
membership-and-marking profiles. -/
theorem prebanana_threeAtom_oneGenerator_profiles_equal :
    prebananaTupleProfile (prebananaUnmarked 2)
      (fun _ : Fin 1 => ({0} : Finset (Fin 3))) =
    prebananaTupleProfile (prebananaUnmarked 2)
      (fun _ : Fin 1 => ({0, 1} : Finset (Fin 3))) := by
  classical
  let xs : Fin 1 → Finset (Fin 3) :=
    fun _ => {0}
  let ys : Fin 1 → Finset (Fin 3) :=
    fun _ => {0, 1}
  have hxs :
      prebananaRealisedSignatures (prebananaUnmarked 2) xs = Finset.univ := by
    exact prebanana_oneGenerator_all_signatures (prebananaUnmarked 2)
      ({0} : Finset (Fin 3))
      (0 : Fin 3) (2 : Fin 3)
      (by simp) (by simp)
  have hys :
      prebananaRealisedSignatures (prebananaUnmarked 2) ys = Finset.univ := by
    exact prebanana_oneGenerator_all_signatures (prebananaUnmarked 2)
      ({0, 1} : Finset (Fin 3))
      (0 : Fin 3) (2 : Fin 3)
      (by simp) (by simp)
  change (prebananaRealisedSignatures (prebananaUnmarked 2) xs,
      prebananaSignatureMark (prebananaUnmarked 2) xs) =
    (prebananaRealisedSignatures (prebananaUnmarked 2) ys,
      prebananaSignatureMark (prebananaUnmarked 2) ys)
  apply Prod.ext
  · rw [hxs, hys]
  · funext p
    simp [prebananaSignatureMark, prebananaUnmarked]

/-- A genuine marked Boolean isomorphism between the two
four-element generated subalgebras of the unmarked three-atom
source. It carries the element {0} to the strictly larger
element {0,1}. -/
noncomputable def prebanana_threeAtom_partialIsomorphism :
    PrebananaGeneratedMarkedIso
      (prebananaUnmarked 2) (prebananaUnmarked 2)
      (fun _ : Fin 1 => ({0} : Finset (Fin 3)))
      (fun _ : Fin 1 => ({0, 1} : Finset (Fin 3))) :=
  prebananaGeneratedMarkedIso_of_profile_eq
    (prebananaUnmarked 2) (prebananaUnmarked 2)
    (fun _ : Fin 1 => ({0} : Finset (Fin 3)))
    (fun _ : Fin 1 => ({0, 1} : Finset (Fin 3)))
    prebanana_threeAtom_oneGenerator_profiles_equal

/-- The partial isomorphism takes the selected generator to its
proper enlargement, as required by the EPPA counterexample. -/
theorem prebanana_threeAtom_partialIsomorphism_generator :
    (prebanana_threeAtom_partialIsomorphism.equiv
      (prebananaTermRange_generator
        (prebananaUnmarked 2)
        (fun _ : Fin 1 => ({0} : Finset (Fin 3))) 0)).val =
      ({0, 1} : Finset (Fin 3)) :=
  prebanana_threeAtom_partialIsomorphism.map_generator 0

end SuccessorTree.NonPrecompact
