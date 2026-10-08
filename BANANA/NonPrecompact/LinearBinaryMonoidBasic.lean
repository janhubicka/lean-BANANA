import BANANA.NonPrecompact.LinearBoringShapeMap
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic

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

/-- A linear map witnessing the action of an injective shape map on one
level is itself injective. -/
theorem levelWitness_injective
    (F : ShapeMap binarySucc)
    {n m : ℕ}
    (φ : (Fin n → F2) →ₗ[F2] (Fin m → F2))
    (hφ :
      ∀ w : AtLevel n,
        ∃ hFw : (F w.1).bits.length = m,
          levelEquiv m ⟨F w.1, hFw⟩ =
            φ (levelEquiv n w)) :
    Function.Injective φ := by
  intro x y hxy
  let wx : AtLevel n := (levelEquiv n).symm x
  let wy : AtLevel n := (levelEquiv n).symm y
  obtain ⟨hFx, hx⟩ := hφ wx
  obtain ⟨hFy, hy⟩ := hφ wy
  let Fx : AtLevel m := ⟨F wx.1, hFx⟩
  let Fy : AtLevel m := ⟨F wy.1, hFy⟩
  have hcoords : levelEquiv m Fx = levelEquiv m Fy := by
    calc
      levelEquiv m Fx = φ (levelEquiv n wx) := hx
      _ = φ (levelEquiv n wy) := by
        rw [(levelEquiv n).apply_symm_apply x,
          (levelEquiv n).apply_symm_apply y]
        exact hxy
      _ = levelEquiv m Fy := hy.symm
  have hsub : Fx = Fy :=
    (levelEquiv m).injective hcoords
  have hword : wx.1 = wy.1 :=
    F.injective (congrArg Subtype.val hsub)
  have hwxy : wx = wy := Subtype.ext hword
  calc
    x = levelEquiv n wx := ((levelEquiv n).apply_symm_apply x).symm
    _ = levelEquiv n wy := by rw [hwxy]
    _ = y := (levelEquiv n).apply_symm_apply y

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

/-- Restrict a coordinate vector to its first `m` coordinates. -/
def prefixRestrictionLinearMap
    (m n : ℕ) (h : m ≤ n) :
    (Fin n → F2) →ₗ[F2] (Fin m → F2) where
  toFun := fun x i => x ⟨i.1, lt_of_lt_of_le i.2 h⟩
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl

/-- Insert one linear coordinate into a finite binary coordinate vector. -/
def insertBoringLinearMap
    (m n : ℕ) (h : m ≤ n)
    (e : LinearBoringRule m) :
    (Fin n → F2) →ₗ[F2] (Fin (n + 1) → F2) where
  toFun := fun x =>
    let p : Fin (n + 1) := ⟨m, Nat.lt_succ_of_le h⟩
    p.insertNth (e (prefixRestrictionLinearMap m n h x)) x
  map_add' := by
    intro x y
    funext j
    let p : Fin (n + 1) := ⟨m, Nat.lt_succ_of_le h⟩
    change
      ((p.insertNth
          (e (prefixRestrictionLinearMap m n h (x + y))) (x + y)) :
        Fin (n + 1) → F2) j =
        ((p.insertNth
          (e (prefixRestrictionLinearMap m n h x)) x) :
          Fin (n + 1) → F2) j +
        ((p.insertNth
          (e (prefixRestrictionLinearMap m n h y)) y) :
          Fin (n + 1) → F2) j
    rw [(prefixRestrictionLinearMap m n h).map_add, e.map_add]
    refine p.succAboveCases ?_ (fun i => ?_) j
    · simp
    · simp [Pi.add_apply]
  map_smul' := by
    intro c x
    funext j
    let p : Fin (n + 1) := ⟨m, Nat.lt_succ_of_le h⟩
    change
      ((p.insertNth
          (e (prefixRestrictionLinearMap m n h (c • x))) (c • x)) :
        Fin (n + 1) → F2) j =
        c • ((p.insertNth
          (e (prefixRestrictionLinearMap m n h x)) x) :
          Fin (n + 1) → F2) j
    rw [(prefixRestrictionLinearMap m n h).map_smul, e.map_smul]
    refine p.succAboveCases ?_ (fun i => ?_) j
    · simp
    · simp [Pi.smul_apply]

/-- On a level reaching the insertion position, the word insertion agrees
with the corresponding linear tuple insertion. -/
theorem levelEquiv_insertLinearCoordinate
    (m n : ℕ) (h : m ≤ n)
    (e : LinearBoringRule m)
    (w : AtLevel n) :
    let hlen :
        (insertLinearCoordinate m e w.1).bits.length = n + 1 := by
      rw [length_insertLinearCoordinate]
      simp [w.2, h]
    levelEquiv (n + 1)
        ⟨insertLinearCoordinate m e w.1, hlen⟩ =
      insertBoringLinearMap m n h e (levelEquiv n w) := by
  intro hlen
  funext j
  let p : Fin (n + 1) := ⟨m, Nat.lt_succ_of_le h⟩
  have hins :
      (insertLinearCoordinate m e w.1).bits =
        w.1.bits.insertIdx m
          (e (prefixCoords w.1 m (by simpa [w.2] using h))) := by
    exact insertLinearCoordinate_of_le
      m e w.1 (by simpa [w.2] using h)
  refine p.succAboveCases ?_ (fun i => ?_) j
  · change
      (insertLinearCoordinate m e w.1).bits.get
          ⟨p.1, by simpa [hlen] using p.2⟩ =
        ((p.insertNth
            (e (prefixRestrictionLinearMap m n h (levelEquiv n w)))
            (levelEquiv n w)) : Fin (n + 1) → F2) p
    simp only [Fin.insertNth_apply_same]
    simp [insertLinearCoordinate, w.2, h,
      prefixRestrictionLinearMap, prefixCoords, levelEquiv,
      List.get_insertIdx_self]
  · change
      (insertLinearCoordinate m e w.1).bits.get
          ⟨(p.succAbove i).1, by simpa [hlen] using (p.succAbove i).2⟩ =
        ((p.insertNth
            (e (prefixRestrictionLinearMap m n h (levelEquiv n w)))
            (levelEquiv n w)) : Fin (n + 1) → F2) (p.succAbove i)
    simp only [Fin.insertNth_apply_succAbove]
    by_cases hi : i.1 < m
    · have hs :
          p.succAbove i = i.castSucc := by
        apply Fin.succAbove_of_castSucc_lt
        change i.1 < m
        exact hi
      rw [hs]
      simp [insertLinearCoordinate, w.2, h, levelEquiv,
        prefixRestrictionLinearMap, prefixCoords, hi,
        List.get_insertIdx_of_lt]
    · have hmi : m ≤ i.1 := Nat.le_of_not_gt hi
      have hs :
          p.succAbove i = i.succ := by
        apply Fin.succAbove_of_le_castSucc
        change m ≤ i.1
        exact hmi
      rw [hs]
      have hk : m + (i.1 - m) = i.1 := by omega
      have hiLength : m + (i.1 - m) < w.1.bits.length := by
        rw [hk, w.2]
        exact i.2
      have hget :=
        List.get_insertIdx_add_succ
          w.1.bits
          (e (prefixCoords w.1 m (by simpa [w.2] using h)))
          m (i.1 - m) hiLength
      rw [hk] at hget
      simpa [insertLinearCoordinate, w.2, h, levelEquiv,
        prefixRestrictionLinearMap, prefixCoords, hi, hmi]
        using hget

/-- Every linear boring coordinate insertion belongs to the levelwise-linear
monoid. -/
theorem linearOnLevels_insertLinearCoordinateShapeMap
    (m : ℕ) (e : LinearBoringRule m) :
    LinearOnLevels (insertLinearCoordinateShapeMap m e) := by
  intro n
  by_cases h : n < m
  · refine ⟨n, LinearMap.id, ?_⟩
    intro w
    have hwlt : w.1.bits.length < m := by simpa [w.2] using h
    have hfix :=
      insertLinearCoordinate_of_lt m e w.1 hwlt
    refine ⟨?_, ?_⟩
    · change (insertLinearCoordinate m e w.1).bits.length = n
      simpa [hfix] using w.2
    · change levelEquiv n
        ⟨insertLinearCoordinate m e w.1, _⟩ = levelEquiv n w
      congr 1
      exact Subtype.ext hfix
  · have hmn : m ≤ n := Nat.le_of_not_gt h
    refine ⟨n + 1, insertBoringLinearMap m n hmn e, ?_⟩
    intro w
    let hlen :
        (insertLinearCoordinate m e w.1).bits.length = n + 1 := by
      rw [length_insertLinearCoordinate]
      simp [w.2, hmn]
    refine ⟨hlen, ?_⟩
    exact levelEquiv_insertLinearCoordinate m n hmn e w

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
    change F (LevelTree.lev w.1) w.1 = F n w.1
    rw [show LevelTree.lev w.1 = n from w.2]
  have hlen :
      (ShapeMap.fusionLimit F hstable w.1).bits.length = m :=
    (congrArg (fun z : BinaryWord => z.bits.length) hpoint).trans hFw
  refine ⟨hlen, ?_⟩
  have hsub :
      (⟨ShapeMap.fusionLimit F hstable w.1, hlen⟩ : AtLevel m) =
        (⟨F n w.1, hFw⟩ : AtLevel m) := Subtype.ext hpoint
  exact (congrArg (levelEquiv m) hsub).trans hw

end BinaryWord
end SuccessorTree.NonPrecompact
