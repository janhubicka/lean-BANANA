import BANANA.NonPrecompact.FolkmanPersistence

/-!
# Composition of partial owners for Folkman atom presentations

For non-unital embeddings, target atoms can be unowned.  Composition
must propagate `none`, and the fibre of a composed owner is the union
of its intermediate owner fibres.

This is a shared combinatorial interface only.  It does not, by itself,
construct an embedding or establish pairing preservation.
-/

namespace SuccessorTree.NonPrecompact

open scoped BigOperators

/-- Compose partial owners in the direction of embeddings:
`g` sends final atoms to intermediate owners; `f` sends
intermediate atoms to source owners. -/
def folkmanComposeOwner
    {q m n : ℕ}
    (f : Fin m → Option (Fin q))
    (g : Fin n → Option (Fin m)) :
    Fin n → Option (Fin q) :=
  fun x => (g x).bind f

/-- The fibre of a composite partial owner is exactly the union
of the final fibres belonging to intermediate atoms owned by `i`.
Unowned intermediate or final atoms do not contribute. -/
theorem folkmanFiber_compose
    {q m n : ℕ}
    (f : Fin m → Option (Fin q))
    (g : Fin n → Option (Fin m))
    (i : Fin q) :
    folkmanFiber (folkmanComposeOwner f g) i =
      (folkmanFiber f i).biUnion (folkmanFiber g) := by
  classical
  ext x
  simp only [folkmanFiber, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_biUnion]
  constructor
  · intro hx
    cases hg : g x with
    | none =>
        simp [folkmanComposeOwner, hg] at hx
    | some j =>
        refine ⟨j, ?_, ?_⟩
        · simpa [folkmanComposeOwner, hg] using hx
        · exact hg
  · rintro ⟨j, hj, hx⟩
    simpa [folkmanComposeOwner, hx] using hj

/-- A source atom remains represented after composition when
every source atom has an intermediate representative and every
intermediate atom has a final representative. -/
theorem folkmanComposeOwner_surjective
    {q m n : ℕ}
    (f : Fin m → Option (Fin q))
    (g : Fin n → Option (Fin m))
    (hf : ∀ i, ∃ j, f j = some i)
    (hg : ∀ j, ∃ x, g x = some j) :
    ∀ i, ∃ x, folkmanComposeOwner f g x = some i := by
  intro i
  obtain ⟨j, hj⟩ := hf i
  obtain ⟨x, hx⟩ := hg j
  exact ⟨x, by simp [folkmanComposeOwner, hx, hj]⟩


/-- Pairing-preserving atom embeddings compose, with unowned target atoms
remaining unowned.  All intermediate sums are taken over actual owner
fibres; no unitality assumption is used. -/
def FolkmanAtomEmbedding.comp
    {A B C : FolkmanAtomStructure}
    (f : FolkmanAtomEmbedding A B)
    (g : FolkmanAtomEmbedding B C) :
    FolkmanAtomEmbedding A C where
  leftOwner := folkmanComposeOwner f.leftOwner g.leftOwner
  rightOwner := folkmanComposeOwner f.rightOwner g.rightOwner
  left_fibre_nonempty := by
    intro i
    rw [folkmanFiber_compose]
    obtain ⟨j, hj⟩ := f.left_fibre_nonempty i
    obtain ⟨x, hx⟩ := g.left_fibre_nonempty j
    exact ⟨x, Finset.mem_biUnion.mpr ⟨j, hj, hx⟩⟩
  right_fibre_nonempty := by
    intro i
    rw [folkmanFiber_compose]
    obtain ⟨j, hj⟩ := f.right_fibre_nonempty i
    obtain ⟨x, hx⟩ := g.right_fibre_nonempty j
    exact ⟨x, Finset.mem_biUnion.mpr ⟨j, hj, hx⟩⟩
  pairing_parity := by
    intro i j
    classical
    simp only [folkmanFiber_compose]
    calc
      (folkmanEdgeCount C.edge
          ((folkmanFiber f.leftOwner i).biUnion (folkmanFiber g.leftOwner))
          ((folkmanFiber f.rightOwner j).biUnion (folkmanFiber g.rightOwner)) : F2) =
        ∑ x ∈ folkmanFiber f.leftOwner i,
          (folkmanEdgeCount C.edge (folkmanFiber g.leftOwner x)
            ((folkmanFiber f.rightOwner j).biUnion
              (folkmanFiber g.rightOwner)) : F2) := by
        rw [folkmanEdgeCount_biUnion_left, Nat.cast_sum]
      _ = ∑ x ∈ folkmanFiber f.leftOwner i,
            ∑ y ∈ folkmanFiber f.rightOwner j,
              (folkmanEdgeCount C.edge (folkmanFiber g.leftOwner x)
                (folkmanFiber g.rightOwner y) : F2) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [folkmanEdgeCount_biUnion_right, Nat.cast_sum]
      _ = ∑ x ∈ folkmanFiber f.leftOwner i,
            ∑ y ∈ folkmanFiber f.rightOwner j,
              B.edge x y := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact g.pairing_parity x y
      _ = (folkmanEdgeCount B.edge
          (folkmanFiber f.leftOwner i)
          (folkmanFiber f.rightOwner j) : F2) :=
        (folkmanEdgeCount_cast B.edge _ _).symm
      _ = A.edge i j := f.pairing_parity i j

end SuccessorTree.NonPrecompact
