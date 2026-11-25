import Mathlib.Dynamics.Transitive
import Mathlib.Topology.Baire.Lemmas

/-!
# Dense orbits of topologically transitive actions

For a topologically transitive action on a second-countable Baire space,
the points with dense orbit form a dense `Gδ` set. Each basis open set
contributes the open dense set of points whose orbit hits it.
-/

namespace SuccessorTree.NonPrecompact

open Filter MulAction Set Topology TopologicalSpace

variable (M : Type*) {X : Type*} [Monoid M] [TopologicalSpace X] [MulAction M X]
  [ContinuousConstSMul M X] [SecondCountableTopology X] [BaireSpace X]
  [MulAction.IsTopologicallyTransitive M X]

/-- A point has a dense orbit exactly when it belongs to the countable
intersection of the open dense sets of points hitting each basis open set. -/
theorem dense_orbit_points_isGδ_and_dense :
    IsGδ {x : X | Dense (orbit M x)} ∧ Dense {x : X | Dense (orbit M x)} := by
  let hit (U : countableBasis X) : Set X := ⋃ g : M, (g • ·) ⁻¹' (U : Set X)
  have hit_open (U : countableBasis X) : IsOpen (hit U) :=
    isOpen_iUnion fun g => (isOpen_of_mem_countableBasis U.2).preimage (continuous_const_smul g)
  have hit_dense (U : countableBasis X) : Dense (hit U) :=
    (isOpen_of_mem_countableBasis U.2).dense_iUnion_preimage_smul M
      (nonempty_of_mem_countableBasis U.2)
  have heq : {x : X | Dense (orbit M x)} = ⋂ U, hit U := by
    ext x
    rw [mem_ofPred_eq, (isBasis_countableBasis X).dense_iff, mem_iInter]
    constructor
    · intro hx U
      obtain ⟨_, hzU, g, rfl⟩ := hx U U.2 (nonempty_of_mem_countableBasis U.2)
      exact mem_iUnion.2 ⟨g, hzU⟩
    · intro hx U hU _
      obtain ⟨g, hg⟩ := mem_iUnion.1 (hx ⟨U, hU⟩)
      exact ⟨g • x, hg, mem_orbit x g⟩
  rw [heq]
  exact ⟨IsGδ.iInter_of_isOpen hit_open, dense_iInter_of_isOpen hit_open hit_dense⟩

/-- Points with dense orbit form a comeagre set. -/
theorem dense_orbit_points_mem_residual :
    {x : X | Dense (orbit M x)} ∈ residual X :=
  let ⟨hGδ, hdense⟩ := dense_orbit_points_isGδ_and_dense M (X := X)
  residual_of_dense_Gδ hGδ hdense

/-- A topologically transitive action on a nonempty second-countable
Baire space has a dense orbit. -/
theorem exists_dense_orbit_of_topologicallyTransitive [Nonempty X] :
    ∃ x : X, Dense (orbit M x) :=
  (dense_orbit_points_isGδ_and_dense M (X := X)).2.nonempty

end SuccessorTree.NonPrecompact
