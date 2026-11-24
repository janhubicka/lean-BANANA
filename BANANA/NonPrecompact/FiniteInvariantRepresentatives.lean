import Mathlib.Data.Fintype.EquivFin

/-!
# Finite representatives from a complete finite invariant

A finite-valued tuple profile gives finitely many representatives
when equality of profiles implies the relation under study. The same
representatives count the classes of a setoid.
-/

namespace SuccessorTree.NonPrecompact

/-- If equality of a finite-valued invariant entails a relation,
the relation admits finitely many source representatives. -/
theorem exists_finite_representatives_of_invariant
    {A K : Type*}
    [Finite K]
    (signature : A → K) (Related : A → A → Prop)
    (hComplete : ∀ a b : A, signature a = signature b →
      Related a b) :
    ∃ representatives : Finset A,
      ∀ a : A, ∃ b ∈ representatives, Related a b := by
  classical
  let : Fintype (Set.range signature) := Fintype.ofFinite _
  let chooseRepresentative (k : Set.range signature) : A :=
    Classical.choose k.property
  refine ⟨Finset.univ.image chooseRepresentative, ?_⟩
  intro a
  let k : Set.range signature := ⟨signature a, a, rfl⟩
  refine ⟨chooseRepresentative k, ?_, ?_⟩
  · exact Finset.mem_image.mpr
      ⟨k, Finset.mem_univ _, rfl⟩
  · exact hComplete a (chooseRepresentative k) (Classical.choose_spec k.property).symm

/-- A finite complete invariant makes the quotient by a setoid finite.
The invariant need not be constant on the equivalence classes. -/
theorem finiteQuotient_of_completeFiniteInvariant
    {X P : Type*} [s : Setoid X] [Finite P]
    (profile : X → P)
    (hcomplete : ∀ x y : X, profile x = profile y → x ≈ y) :
    Finite (Quotient s) := by
  obtain ⟨reps, hcover⟩ :=
    exists_finite_representatives_of_invariant profile s.r hcomplete
  apply Finite.of_surjective (fun y : reps => (⟦y.val⟧ : Quotient s))
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  obtain ⟨y, hy, hxy⟩ := hcover x
  exact ⟨⟨y, hy⟩, (Quotient.sound hxy).symm⟩

end SuccessorTree.NonPrecompact
