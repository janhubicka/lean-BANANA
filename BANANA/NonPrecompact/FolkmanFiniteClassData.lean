import BANANA.NonPrecompact.FolkmanPersistence
import BANANA.NonPrecompact.FolkmanNativeNonUnitalRingOwners

/-!
# Elementary finite-class properties of Folkman--BANANA

The atom presentation consists of two finite atom sets and a binary
F₂-matrix between them.  This module proves that the family of finite
atom presentations is countable and contains structures with arbitrarily
many atoms in both sorts.

For native Boolean rings, restriction along non-unital homomorphisms
preserves biadditivity of the pairing.  This supplies the hereditary
pairing step for the original two-sorted language.

Joint embedding and the full Fraïssé-class packaging are separate.
-/

namespace SuccessorTree.NonPrecompact

/-- Complete finite atom code of a Folkman structure. -/
def folkmanAtomStructureCode (A : FolkmanAtomStructure) :
    Σ l : ℕ, Σ r : ℕ, Fin l → Fin r → F2 :=
  ⟨A.leftCount, ⟨A.rightCount, A.edge⟩⟩

/-- The complete atom code determines its Folkman presentation. -/
theorem folkmanAtomStructureCode_injective :
    Function.Injective folkmanAtomStructureCode := by
  rintro ⟨l, r, edge⟩ ⟨l', r', edge'⟩ h
  cases h
  rfl

/-- There are countably many finite Folkman atom presentations.
Consequently their isomorphism types form a countable family. -/
noncomputable instance folkmanAtomStructureCountable :
    Countable FolkmanAtomStructure := by
  classical
  exact folkmanAtomStructureCode_injective.countable

/-- Arbitrarily large finite Folkman structures with zero pairing. -/
def FolkmanAtomStructure.zeroPairing (l r : ℕ) : FolkmanAtomStructure where
  leftCount := l
  rightCount := r
  edge := fun _ _ => 0

/-- The finite Folkman class has no bound on the number of atoms in
either Boolean-ring sort. -/
theorem folkmanAtomStructure_unbounded_both_sorts (n : ℕ) :
    ∃ A : FolkmanAtomStructure,
      n < A.leftCount ∧ n < A.rightCount := by
  exact ⟨FolkmanAtomStructure.zeroPairing (n + 1) (n + 1),
    Nat.lt_succ_self n, Nat.lt_succ_self n⟩

/-- Restrict an F₂-valued pairing along arbitrary native non-unital
Boolean-ring homomorphisms in both sorts. -/
def folkmanNativePullbackPairing
    {L R L' R' : Type*}
    [BooleanRing L] [BooleanRing R]
    [BooleanRing L'] [BooleanRing R']
    (γ : L → R → F2)
    (fL : L' →ₙ+* L) (fR : R' →ₙ+* R) :
    L' → R' → F2 :=
  fun x y => γ (fL x) (fR y)

/-- Pullback preserves additivity in the left ring. -/
theorem folkmanNativePullbackPairing_add_left
    {L R L' R' : Type*}
    [BooleanRing L] [BooleanRing R]
    [BooleanRing L'] [BooleanRing R']
    (γ : L → R → F2)
    (fL : L' →ₙ+* L) (fR : R' →ₙ+* R)
    (hleft : ∀ x x' y, γ (x + x') y = γ x y + γ x' y)
    (x x' : L') (y : R') :
    folkmanNativePullbackPairing γ fL fR (x + x') y =
      folkmanNativePullbackPairing γ fL fR x y +
        folkmanNativePullbackPairing γ fL fR x' y := by
  change γ (fL (x + x')) (fR y) =
    γ (fL x) (fR y) + γ (fL x') (fR y)
  rw [map_add, hleft]

/-- Pullback preserves additivity in the right ring. -/
theorem folkmanNativePullbackPairing_add_right
    {L R L' R' : Type*}
    [BooleanRing L] [BooleanRing R]
    [BooleanRing L'] [BooleanRing R']
    (γ : L → R → F2)
    (fL : L' →ₙ+* L) (fR : R' →ₙ+* R)
    (hright : ∀ x y y', γ x (y + y') = γ x y + γ x y')
    (x : L') (y y' : R') :
    folkmanNativePullbackPairing γ fL fR x (y + y') =
      folkmanNativePullbackPairing γ fL fR x y +
        folkmanNativePullbackPairing γ fL fR x y' := by
  change γ (fL x) (fR (y + y')) =
    γ (fL x) (fR y) + γ (fL x) (fR y')
  rw [map_add, hright]

/-- Hereditary pairing certificate: the restriction of a bilinear
Folkman pairing along a pair of non-unital ring maps is again bilinear. -/
theorem folkmanNativePullbackPairing_bilinear
    {L R L' R' : Type*}
    [BooleanRing L] [BooleanRing R]
    [BooleanRing L'] [BooleanRing R']
    (γ : L → R → F2)
    (fL : L' →ₙ+* L) (fR : R' →ₙ+* R)
    (hleft : ∀ x x' y, γ (x + x') y = γ x y + γ x' y)
    (hright : ∀ x y y', γ x (y + y') = γ x y + γ x y') :
    (∀ x x' y,
      folkmanNativePullbackPairing γ fL fR (x + x') y =
        folkmanNativePullbackPairing γ fL fR x y +
          folkmanNativePullbackPairing γ fL fR x' y) ∧
    (∀ x y y',
      folkmanNativePullbackPairing γ fL fR x (y + y') =
        folkmanNativePullbackPairing γ fL fR x y +
          folkmanNativePullbackPairing γ fL fR x y') := by
  constructor
  · intro x x' y
    exact folkmanNativePullbackPairing_add_left γ fL fR hleft x x' y
  · intro x y y'
    exact folkmanNativePullbackPairing_add_right γ fL fR hright x y y'

end SuccessorTree.NonPrecompact
