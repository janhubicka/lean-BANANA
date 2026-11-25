import Mathlib.ModelTheory.Fraisse
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.MulAction

/-!
# The pointwise automorphism group of a first-order structure

First-order automorphisms form a topological group with the topology of
pointwise convergence on the discrete structure. They act continuously
on embeddings of finite structures, given the discrete topology.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder Set Filter Topology
open scoped FirstOrder

/-- The group of all language automorphisms, separated from the underlying
first-order equivalence type so that it can carry its group and topology. -/
def FirstOrderAut (L : Language) (M : Type*) [L.Structure M] := M ≃[L] M

namespace FirstOrderAut

variable {L : Language} {M : Type*} [L.Structure M]

/-- Regard an automorphism as a first-order equivalence. -/
def toEquiv (g : FirstOrderAut L M) : M ≃[L] M := g

/-- Regard a first-order equivalence as an automorphism. -/
def ofEquiv (g : M ≃[L] M) : FirstOrderAut L M := g

instance : Group (FirstOrderAut L M) where
  mul g h := ofEquiv (g.toEquiv.comp h.toEquiv)
  one := ofEquiv (Language.Equiv.refl L M)
  inv g := ofEquiv g.toEquiv.symm
  mul_assoc g h k := Language.Equiv.comp_assoc k.toEquiv h.toEquiv g.toEquiv
  one_mul g := Language.Equiv.refl_comp g.toEquiv
  mul_one g := Language.Equiv.comp_refl g.toEquiv
  inv_mul_cancel g := Language.Equiv.symm_comp_self g.toEquiv

instance : MulAction (FirstOrderAut L M) M where
  smul g x := g.toEquiv x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

private def discreteValue (a : M) : WithDiscreteTopology M := WithTopology.toTopology ⊥ a

private def evaluation (g : FirstOrderAut L M) : M → WithDiscreteTopology M :=
  fun a => discreteValue (g.toEquiv a)

instance : TopologicalSpace (FirstOrderAut L M) := .induced evaluation inferInstance

private theorem continuous_evaluation (a : M) :
    Continuous (fun g : FirstOrderAut L M => evaluation g a) := by
  have h : Continuous (evaluation (L := L) (M := M)) := continuous_induced_dom
  exact (continuous_apply a).comp h

theorem isOpen_eval (a b : M) : IsOpen {g : FirstOrderAut L M | g.toEquiv a = b} := by
  convert (isOpen_discrete ({discreteValue b} : Set (WithDiscreteTopology M))).preimage
    (continuous_evaluation (L := L) a) using 1
  ext g
  exact (WithTopology.toTopology_injective (⊥ : TopologicalSpace M)).eq_iff.symm

instance : IsTopologicalGroup (FirstOrderAut L M) where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    apply continuous_discrete_rng.mpr
    intro b
    obtain ⟨b, rfl⟩ := (WithTopology.toTopology_surjective (⊥ : TopologicalSpace M)) b
    have hfib :
        (fun p : FirstOrderAut L M × FirstOrderAut L M =>
          evaluation (p.1 * p.2) a) ⁻¹' {discreteValue b} =
        ⋃ c : M, {g : FirstOrderAut L M | g.toEquiv c = b} ×ˢ
          {g : FirstOrderAut L M | g.toEquiv a = c} := by
      ext p
      change discreteValue (p.1.toEquiv (p.2.toEquiv a)) = discreteValue b ↔ _
      rw [(WithTopology.toTopology_injective (⊥ : TopologicalSpace M)).eq_iff]
      simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨p.2.toEquiv a, h, rfl⟩, fun ⟨c, hc, hc'⟩ => hc' ▸ hc⟩
    change IsOpen ((fun p : FirstOrderAut L M × FirstOrderAut L M =>
      evaluation (p.1 * p.2) a) ⁻¹' {discreteValue b})
    rw [hfib]
    exact isOpen_iUnion fun c => (isOpen_eval c b).prod (isOpen_eval a c)
  continuous_inv := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro a
    apply continuous_discrete_rng.mpr
    intro b
    obtain ⟨b, rfl⟩ := (WithTopology.toTopology_surjective (⊥ : TopologicalSpace M)) b
    convert isOpen_eval (L := L) b a using 1
    ext g
    change discreteValue (g.toEquiv.symm a) = discreteValue b ↔ g.toEquiv b = a
    rw [(WithTopology.toTopology_injective (⊥ : TopologicalSpace M)).eq_iff]
    exact (g.toEquiv.toEquiv.symm_apply_eq).trans eq_comm

/-- Equality of evaluations on a fixed finite tuple is an open
condition in the pointwise topology. -/
theorem isOpen_tupleEval {n : ℕ} (a b : Fin n → M) :
    IsOpen {g : FirstOrderAut L M | ∀ i, g.toEquiv (a i) = b i} := by
  rw [show {g : FirstOrderAut L M | ∀ i, g.toEquiv (a i) = b i} =
      ⋂ i : Fin n, {g : FirstOrderAut L M | g.toEquiv (a i) = b i} from by ext g; simp]
  exact isOpen_iInter_of_finite fun i => isOpen_eval (a i) (b i)

/-- Agreement on finitely many points gives a neighbourhood basis for
pointwise convergence. The finite points are listed in a tuple. -/
theorem exists_tupleEval_subset_of_mem_nhds (g : FirstOrderAut L M)
    (U : Set (FirstOrderAut L M)) (hU : U ∈ 𝓝 g) :
    ∃ n : ℕ, ∃ a : Fin n → M,
      {h : FirstOrderAut L M | ∀ i, h.toEquiv (a i) = g.toEquiv (a i)} ⊆ U := by
  classical
  change U ∈ @nhds _ (TopologicalSpace.induced evaluation inferInstance) g at hU
  rw [nhds_induced, Filter.mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨I, W, hW, hWV⟩ := hV
  let E := Fintype.equivFin I
  let a (i : Fin (Fintype.card I)) : M := E.symm i
  refine ⟨Fintype.card I, a, fun h hh => hVU (hWV ?_)⟩
  intro i hi
  have heq := hh (E ⟨i, hi⟩)
  change h.toEquiv (a (E ⟨i, hi⟩)) = g.toEquiv (a (E ⟨i, hi⟩)) at heq
  have heval : evaluation h i = evaluation g i := by
    simpa only [a, Equiv.symm_apply_apply, evaluation] using congrArg discreteValue heq
  rw [heval]
  exact mem_of_mem_nhds (hW i)

variable {A : Type*} [L.Structure A]

instance : MulAction (FirstOrderAut L M) (A ↪[L] M) where
  smul g e := g.toEquiv.toEmbedding.comp e
  one_smul e := by ext x; rfl
  mul_smul g h e := by ext x; rfl

theorem isOpen_embedding_eval [Finite A] (e f : A ↪[L] M) :
    IsOpen {g : FirstOrderAut L M | g • e = f} := by
  have hset : {g : FirstOrderAut L M | g • e = f} =
      ⋂ a : A, {g : FirstOrderAut L M | g.toEquiv (e a) = f a} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h a
      exact DFunLike.congr_fun h a
    · intro h
      exact FirstOrder.Language.Embedding.ext h
  rw [hset]
  exact isOpen_iInter_of_finite fun a => isOpen_eval (e a) (f a)

/-- The automorphism action on finite embeddings is continuous in the
discrete topology on the embedding space. -/
theorem continuous_embedding_smul [Finite A]
    [TopologicalSpace (A ↪[L] M)] [DiscreteTopology (A ↪[L] M)] :
    ContinuousSMul (FirstOrderAut L M) (A ↪[L] M) := by
  constructor
  apply continuous_prod_of_discrete_right.mpr
  intro e
  apply continuous_discrete_rng.mpr
  exact fun f => isOpen_embedding_eval e f

/-- Homogeneity makes the action transitive on embeddings of one finite
structure (if any such embedding exists). -/
theorem exists_smul_eq_embedding [Finite A] (hM : L.IsUltrahomogeneous M)
    (e f : A ↪[L] M) : ∃ g : FirstOrderAut L M, g • e = f := by
  obtain ⟨g, hg⟩ := hM e.toHom.range ((Language.Structure.FG.of_finite (L := L)
    (M := A)).range e.toHom) (f.comp e.equivRange.symm.toEmbedding)
  refine ⟨ofEquiv g, ?_⟩
  ext a
  have h := DFunLike.congr_fun hg (e.equivRange a)
  change g (e a) = f a
  simpa using h.symm

end FirstOrderAut

end SuccessorTree.NonPrecompact
