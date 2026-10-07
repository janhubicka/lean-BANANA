import BANANA.NonPrecompact.LinearBoringShapeMap
import Mathlib.Data.List.OfFn

/-!
# Levelwise-linear shape maps on the binary prefix tree

A shape map is in the vector-space monoid when its action on every fixed
source level is a linear map between the corresponding binary coordinate
spaces.  This file proves the M1 closure properties: identity, composition,
and pointwise fusion preserve levelwise linearity.
-/

namespace SuccessorTree.NonPrecompact
namespace BinaryWord

/-- Binary words of exactly one level. -/
abbrev AtLevel (n : ℕ) :=
  {w : BinaryWord // w.bits.length = n}

/-- Identify the n-th level of the binary tree with F₂^n. -/
def levelEquiv (n : ℕ) : AtLevel n ≃ (Fin n → F2) where
  toFun := fun w i =>
    w.1.bits.get
      ⟨i.1, by simpa [w.2] using i.2⟩
  invFun := fun x =>
    ⟨⟨List.ofFn x⟩, by simp⟩
  left_inv := by
    intro w
    apply Subtype.ext
    apply BinaryWord.ext
    rcases w with ⟨⟨bits⟩, hbits⟩
    dsimp
    subst n
    simp
  right_inv := by
    intro x
    funext i
    simp

/-- A shape map is linear on levels when each level action, after the
canonical identification with a coordinate vector space, is induced by a
linear map. -/
def LinearOnLevels (F : ShapeMap binarySucc) : Prop :=
  ∀ n : ℕ,
    ∃ m : ℕ,
      ∃ φ : (Fin n → F2) →ₗ[F2] (Fin m → F2),
        ∀ w : AtLevel n,
          ∃ hFw : (F w.1).bits.length = m,
            levelEquiv m ⟨F w.1, hFw⟩ =
              φ (levelEquiv n w)

/-- Levelwise linearity forces the all-zero word on every source level to
map to the all-zero word on the corresponding target level. -/
theorem LinearOnLevels.map_zero
    {F : ShapeMap binarySucc}
    (hF : LinearOnLevels F) (n : ℕ) :
    let w0 : AtLevel n :=
      ⟨⟨List.replicate n 0⟩, by simp⟩
    ∃ m : ℕ, ∃ hlen : (F w0.1).bits.length = m,
      levelEquiv m ⟨F w0.1, hlen⟩ = 0 := by
  intro w0
  obtain ⟨m, φ, hφ⟩ := hF n
  obtain ⟨hlen, hw⟩ := hφ w0
  refine ⟨m, hlen, ?_⟩
  have hz : levelEquiv n w0 = 0 := by
    funext i
    simp [w0, levelEquiv]
  rw [hw, hz, φ.map_zero]

theorem linearOnLevels_id :
    LinearOnLevels (ShapeMap.id binarySucc) := by
  intro n
  refine ⟨n, LinearMap.id, ?_⟩
  intro w
  refine ⟨w.2, ?_⟩
  rfl

theorem linearOnLevels_comp
    {F G : ShapeMap binarySucc}
    (hF : LinearOnLevels F)
    (hG : LinearOnLevels G) :
    LinearOnLevels (F.comp G) := by
  intro n
  obtain ⟨m, ψ, hψ⟩ := hG n
  obtain ⟨l, φ, hφ⟩ := hF m
  refine ⟨l, φ.comp ψ, ?_⟩
  intro w
  obtain ⟨hGw, hwG⟩ := hψ w
  let Gw : AtLevel m := ⟨G w.1, hGw⟩
  obtain ⟨hFGw, hGwF⟩ := hφ Gw
  refine ⟨hFGw, ?_⟩
  change levelEquiv l ⟨F (G w.1), hFGw⟩ =
    φ (ψ (levelEquiv n w))
  calc
    levelEquiv l ⟨F (G w.1), hFGw⟩ =
        φ (levelEquiv m Gw) := hGwF
    _ = φ (ψ (levelEquiv n w)) := by rw [hwG]

/-- The pointwise fusion limit inherits the levelwise linear map from the
stage indexed by the source level. -/
theorem linearOnLevels_fusionLimit
    (F : ℕ → ShapeMap binarySucc)
    (hmem : ∀ i, LinearOnLevels (F i))
    (hstable : ShapeMap.FusionStable F) :
    LinearOnLevels (ShapeMap.fusionLimit F hstable) := by
  intro n
  obtain ⟨m, φ, hφ⟩ := hmem n n
  refine ⟨m, φ, ?_⟩
  intro w
  obtain ⟨hFw, hw⟩ := hφ w
  have hpoint :
      ShapeMap.fusionLimit F hstable w.1 = F n w.1 := by
    simpa [w.2] using
      ShapeMap.fusionLimit_apply F hstable w.1
  refine ⟨?_, ?_⟩
  · simpa [hpoint] using hFw
  · simpa [hpoint] using hw

end BinaryWord
end SuccessorTree.NonPrecompact
