import BANANA.NonPrecompact.BananaLimitTupleSignatures

/-!
# Finite representatives from a complete finite invariant

This is a general finite-orbit counting device, independent of
the group action. If a map into a finite type determines when two
objects are related, then the relation has a finite collection of
representatives. The intended application is the explicit BANANA
limit, where the invariant consists of linear relations and a finite
matrix of pairings.

This theorem by itself makes no claims about the completeness of the
BANANA tuple invariant.
-/

namespace SuccessorTree.NonPrecompact

/-- If equality of a finite-valued invariant entails a relation,
the relation admits finitely many source representatives. -/
theorem exists_finite_representatives_of_invariant
    {A K : Type*}
    [Inhabited A] [Fintype K]
    (signature : A → K) (Related : A → A → Prop)
    (hComplete : ∀ a b : A, signature a = signature b →
      Related a b) :
    ∃ representatives : Finset A,
      ∀ a : A, ∃ b ∈ representatives, Related a b := by
  classical
  let chooseRepresentative : K → A := fun k =>
    if h : ∃ a : A, signature a = k then Classical.choose h
    else default
  refine ⟨Finset.univ.image chooseRepresentative, ?_⟩
  intro a
  have hSig : signature (chooseRepresentative (signature a)) =
      signature a := by
    dsimp [chooseRepresentative]
    split_ifs with h
    · exact Classical.choose_spec h
    · exact False.elim (h ⟨a, rfl⟩)
  refine ⟨chooseRepresentative (signature a), ?_, ?_⟩
  · exact Finset.mem_image.mpr
      ⟨signature a, Finset.mem_univ _, rfl⟩
  · exact hComplete a (chooseRepresentative (signature a)) hSig.symm

end SuccessorTree.NonPrecompact
