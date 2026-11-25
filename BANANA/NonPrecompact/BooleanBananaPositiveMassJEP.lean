import BANANA.NonPrecompact.BooleanBananaPositiveMassStrongAP
import BANANA.NonPrecompact.BooleanBananaPositiveMassReasonable

/-!
# Joint embedding for the finite positive-mass expansion

The one-atom algebra has mass two and zero marking. It embeds into
all finite positive-mass algebras, so the checked strong amalgamation
property gives joint embedding.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

open scoped BigOperators Classical

private def oneAtomEmbedding (A : Type*) [BooleanAlgebra A] :
    BoundedLatticeHom (Finset (Fin 1)) A where
  toFun s := if (0 : Fin 1) ∈ s then ⊤ else ⊥
  map_bot' := by simp
  map_top' := by simp
  map_sup' s t := by
    by_cases hs : (0 : Fin 1) ∈ s <;> by_cases ht : (0 : Fin 1) ∈ t <;> simp [hs, ht]
  map_inf' s t := by
    by_cases hs : (0 : Fin 1) ∈ s <;> by_cases ht : (0 : Fin 1) ∈ t <;> simp [hs, ht]

private theorem oneAtomEmbedding_injective {A : Type*} [BooleanAlgebra A]
    (h : (⊤ : A) ≠ ⊥) :
    Function.Injective (oneAtomEmbedding A) := by
  intro s t heq
  ext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  by_cases hs : (0 : Fin 1) ∈ s <;> by_cases ht : (0 : Fin 1) ∈ t <;>
    simp [oneAtomEmbedding, hs, ht, h, Ne.symm h] at heq ⊢

private theorem mass_top_ne_bot {A : Type*} [BooleanAlgebra A]
    {S : Set ℕ} {μ : A → ZMod 2} {ρ : A → ℚ} (h : IsFinitePositiveMass S μ ρ) :
    (⊤ : A) ≠ ⊥ := by
  intro heq
  have hz := congrArg ρ heq
  rw [h.mass_top, h.mass_bot] at hz
  exact (by decide : (2 : ℚ) ≠ 0) hz

private def oneAtomWeight (S : Set ℕ) (_ : Fin 1) : PositiveMassWeight S :=
  ⟨2, 1, by decide, (positiveMassDenominators S).one_mem⟩

private theorem oneAtomEmbedding_preserves_mass {A : Type*} [BooleanAlgebra A]
    {S : Set ℕ} {μ : A → ZMod 2} {ρ : A → ℚ} (h : IsFinitePositiveMass S μ ρ)
    (s : Finset (Fin 1)) :
    ρ (oneAtomEmbedding A s) = ∑ i ∈ s, (oneAtomWeight S i).mass := by
  have hsub (i : Fin 1) : i = 0 := Subsingleton.elim _ _
  by_cases hs : (0 : Fin 1) ∈ s
  · have hsu : s = Finset.univ := by ext i; rw [hsub i]; simp [hs]
    rw [hsu]
    simp [oneAtomEmbedding, oneAtomWeight, PositiveMassWeight.mass, h.mass_top]
  · have hz : s = ∅ := by ext i; rw [hsub i]; simp [hs]
    rw [hz]
    simp [oneAtomEmbedding, h.mass_bot]

/-- Any two finite positive-mass algebras embed into one finite
positive-mass algebra. The embeddings preserve both functions and the
actual Boolean operations. -/
theorem positiveMass_jointEmbedding
    {B C : Type} [BooleanAlgebra B] [Fintype B] [BooleanAlgebra C] [Fintype C]
    {S : Set ℕ} {p : ℕ} (hpS : p ∈ S) (hp : p.Prime) (hpOdd : Odd p)
    {μB : B → ZMod 2} {ρB : B → ℚ} {μC : C → ZMod 2} {ρC : C → ℚ}
    (hB : IsFinitePositiveMass S μB ρB) (hC : IsFinitePositiveMass S μC ρC) :
    ∃ (I : Type) (fi : Fintype I) (de : DecidableEq I),
      letI := fi
      letI := de
      ∃ (μD : Finset I → ZMod 2) (ρD : Finset I → ℚ),
        IsFinitePositiveMass S μD ρD ∧
        ∃ (i : BoundedLatticeHom B (Finset I)) (j : BoundedLatticeHom C (Finset I)),
          Function.Injective i ∧ Function.Injective j ∧
          (∀ b, ρD (i b) = ρB b ∧ μD (i b) = μB b) ∧
          (∀ c, ρD (j c) = ρC c ∧ μD (j c) = μC c) := by
  classical
  let w := oneAtomWeight S
  have htotal : ∑ i : Fin 1, (w i).mass = 2 := by
    simp [w, oneAtomWeight, PositiveMassWeight.mass]
  have hA := weightedPowerset_isFinitePositiveMass w htotal
  obtain ⟨I, fi, de, μD, ρD, hD, i, j, hi, hj, hip, hjp, _, _⟩ :=
    positiveMass_strongAmalgamation hpS hp hpOdd hA hB hC
      (oneAtomEmbedding B) (oneAtomEmbedding C)
      (oneAtomEmbedding_injective (mass_top_ne_bot hB))
      (oneAtomEmbedding_injective (mass_top_ne_bot hC))
      (oneAtomEmbedding_preserves_mass hB)
      (oneAtomEmbedding_preserves_mass hC)
  exact ⟨I, fi, de, μD, ρD, hD, i, j, hi, hj, hip, hjp⟩

/-- Every admissibly marked nontrivial finite Boolean algebra admits a
positive S-mass as soon as S contains one permitted odd prime. -/
theorem positiveMass_admitsExpansion
    {B : Type*} [BooleanAlgebra B] [Fintype B] [Nontrivial B]
    {S : Set ℕ} {p : ℕ} (hpS : p ∈ S) (hp : p.Prime) (hpOdd : Odd p)
    (μB : B → ZMod 2) (hbot : μB ⊥ = 0) (htop : μB ⊤ = 0)
    (hadd : ∀ x y, x ⊓ y = ⊥ → μB (x ⊔ y) = μB x + μB y) :
    ∃ ρB : B → ℚ, IsFinitePositiveMass S μB ρB := by
  classical
  let w := oneAtomWeight S
  have htotal : ∑ i : Fin 1, (w i).mass = 2 := by
    simp [w, oneAtomWeight, PositiveMassWeight.mass]
  have hA := weightedPowerset_isFinitePositiveMass w htotal
  have hzero (i : Fin 1) : (w i).parity = 0 := by
    change (2 : ZMod 2) = 0
    decide
  have hmark (s : Finset (Fin 1)) :
      μB (oneAtomEmbedding B s) = ∑ i ∈ s, (w i).parity := by
    change μB (if (0 : Fin 1) ∈ s then ⊤ else ⊥) = _
    by_cases hs : (0 : Fin 1) ∈ s <;> simp [hs, hbot, htop, hzero]
  obtain ⟨ρ, hρ, _⟩ := positiveMass_reasonable hpS hp hpOdd hA μB hbot hadd
    (oneAtomEmbedding B) (oneAtomEmbedding_injective top_ne_bot) hmark
  exact ⟨ρ, hρ⟩

end SuccessorTree.NonPrecompact.BooleanBanana
