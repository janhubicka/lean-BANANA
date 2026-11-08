import BANANA.NonPrecompact.FolkmanPersistence

/-!
# Composition of partial owners for Folkman atom presentations

For non-unital embeddings, target atoms can be unowned.  Composition
must propagate `none`, and the fibre of a composed owner is the union
of its intermediate owner fibres.

This module constructs composition of actual atom-coordinate Folkman
embeddings, preserving their pairing.  It does not construct or classify
embeddings of the original non-unital Boolean rings.
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


/-- The identity partial owner assigns every atom to itself. -/
def folkmanIdentityOwner (q : ℕ) : Fin q → Option (Fin q) :=
  fun i => some i

theorem folkmanComposeOwner_id_left
    {q n : ℕ} (f : Fin n → Option (Fin q)) :
    folkmanComposeOwner (folkmanIdentityOwner q) f = f := by
  funext x
  cases h : f x with
  | none => simp [folkmanComposeOwner, folkmanIdentityOwner, h]
  | some i => simp [folkmanComposeOwner, folkmanIdentityOwner, h]

theorem folkmanComposeOwner_id_right
    {q n : ℕ} (f : Fin n → Option (Fin q)) :
    folkmanComposeOwner f (folkmanIdentityOwner n) = f := by
  funext x
  simp [folkmanComposeOwner, folkmanIdentityOwner]

theorem folkmanComposeOwner_assoc
    {q m n p : ℕ}
    (f : Fin m → Option (Fin q))
    (g : Fin n → Option (Fin m))
    (h : Fin p → Option (Fin n)) :
    folkmanComposeOwner (folkmanComposeOwner f g) h =
      folkmanComposeOwner f (folkmanComposeOwner g h) := by
  funext x
  cases hh : h x with
  | none => simp [folkmanComposeOwner, hh]
  | some j =>
      cases hg : g j with
      | none => simp [folkmanComposeOwner, hh, hg]
      | some k => simp [folkmanComposeOwner, hh, hg]

/-- Two atom embeddings with the same owners are equal.  The remaining
fields are propositions, so proof irrelevance applies. -/
theorem folkmanAtomEmbedding_eq_of_owners
    {A B : FolkmanAtomStructure}
    {f g : FolkmanAtomEmbedding A B}
    (hl : f.leftOwner = g.leftOwner)
    (hr : f.rightOwner = g.rightOwner) : f = g := by
  cases f with
  | mk fl fr flne frne fp =>
      cases g with
      | mk gl gr glne grne gp =>
          cases hl
          cases hr
          rfl

/-- Identity embedding for a finite Folkman atom structure. -/
def FolkmanAtomEmbedding.id (A : FolkmanAtomStructure) :
    FolkmanAtomEmbedding A A where
  leftOwner := folkmanIdentityOwner A.leftCount
  rightOwner := folkmanIdentityOwner A.rightCount
  left_fibre_nonempty := by
    intro i
    exact ⟨i, by simp [folkmanFiber, folkmanIdentityOwner]⟩
  right_fibre_nonempty := by
    intro j
    exact ⟨j, by simp [folkmanFiber, folkmanIdentityOwner]⟩
  pairing_parity := by
    intro i j
    have hl : folkmanFiber (folkmanIdentityOwner A.leftCount) i = {i} := by
      ext x
      simp [folkmanFiber, folkmanIdentityOwner]
    have hr : folkmanFiber (folkmanIdentityOwner A.rightCount) j = {j} := by
      ext y
      simp [folkmanFiber, folkmanIdentityOwner]
    rw [hl, hr, folkmanEdgeCount_cast]
    simp

theorem FolkmanAtomEmbedding.id_comp
    {A B : FolkmanAtomStructure} (f : FolkmanAtomEmbedding A B) :
    (FolkmanAtomEmbedding.id A).comp f = f := by
  apply folkmanAtomEmbedding_eq_of_owners
  · exact folkmanComposeOwner_id_left f.leftOwner
  · exact folkmanComposeOwner_id_left f.rightOwner

theorem FolkmanAtomEmbedding.comp_id
    {A B : FolkmanAtomStructure} (f : FolkmanAtomEmbedding A B) :
    f.comp (FolkmanAtomEmbedding.id B) = f := by
  apply folkmanAtomEmbedding_eq_of_owners
  · exact folkmanComposeOwner_id_right f.leftOwner
  · exact folkmanComposeOwner_id_right f.rightOwner

theorem FolkmanAtomEmbedding.comp_assoc
    {A B C D : FolkmanAtomStructure}
    (f : FolkmanAtomEmbedding A B)
    (g : FolkmanAtomEmbedding B C)
    (h : FolkmanAtomEmbedding C D) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply folkmanAtomEmbedding_eq_of_owners
  · exact folkmanComposeOwner_assoc f.leftOwner g.leftOwner h.leftOwner
  · exact folkmanComposeOwner_assoc f.rightOwner g.rightOwner h.rightOwner

end SuccessorTree.NonPrecompact
