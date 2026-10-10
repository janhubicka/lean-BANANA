import BANANA.NonPrecompact.CompletionAmbientAction
import BANANA.NonPrecompact.FinitePerfectGL

/-!
# Simultaneous automorphisms of three orthogonal perfect blocks

A perfect pairing decomposed as A ⊥ B₀ ⊥ C₀ carries a
block-diagonal automorphism from any prescribed linear
automorphisms of its three left factors, with the corresponding
contragredient actions on the right.

These identities constitute the standard-coordinate core of the
amalgamation of perfect total finite systems in the ample-generics
proof. They do not yet construct arbitrary orthogonal complements
or formalise WAP for general systems.
-/

namespace SuccessorTree.NonPrecompact

open scoped Matrix

/-- Simultaneous action on three consecutive standard perfect blocks. -/
noncomputable def bananaPerfectTripleLeft
    {a b c : ℕ}
    (fA : FinitePerfectGL a)
    (fB : FinitePerfectGL b)
    (fC : FinitePerfectGL c) :
    FinitePerfectGL (a + (b + c)) :=
  BananaMatrixStructure.directSumLinearEquiv fA
    (BananaMatrixStructure.directSumLinearEquiv fB fC)

/-- Simultaneous automorphism on both sorts, the right action being
determined by the contragredient. -/
noncomputable def bananaPerfectTripleAutomorphism
    {a b c : ℕ}
    (fA : FinitePerfectGL a)
    (fB : FinitePerfectGL b)
    (fC : FinitePerfectGL c) :
    BananaMatrixEmbedding
      (perfectBanana (a + (b + c)))
      (perfectBanana (a + (b + c))) :=
  perfectPairAutomorphismOfLinearEquiv
    (bananaPerfectTripleLeft fA fB fC)

/-- Its left action extends the automorphism of the shared first block. -/
theorem bananaPerfectTriple_left_first
    {a b c : ℕ}
    (fA : FinitePerfectGL a)
    (fB : FinitePerfectGL b)
    (fC : FinitePerfectGL c)
    (x : Fin a → F2) :
    (bananaPerfectTripleAutomorphism fA fB fC).left
      (Fin.append x (0 : Fin (b + c) → F2)) =
      Fin.append (fA x) (0 : Fin (b + c) → F2) := by
  change
    (BananaMatrixStructure.directSumLinearEquiv fA
      (BananaMatrixStructure.directSumLinearEquiv fB fC))
      (Fin.append x (0 : Fin (b + c) → F2)) = _
  rw [BananaMatrixStructure.directSumLinearEquiv_apply]
  simp only [BananaMatrixStructure.finLeftPart_append,
    BananaMatrixStructure.finRightPart_append, map_zero]

/-- The left action has the specified restriction to the second block. -/
theorem bananaPerfectTriple_left_second
    {a b c : ℕ}
    (fA : FinitePerfectGL a)
    (fB : FinitePerfectGL b)
    (fC : FinitePerfectGL c)
    (x : Fin b → F2) :
    (bananaPerfectTripleAutomorphism fA fB fC).left
      (Fin.append (0 : Fin a → F2)
        (Fin.append x (0 : Fin c → F2))) =
      Fin.append (0 : Fin a → F2)
        (Fin.append (fB x) (0 : Fin c → F2)) := by
  change bananaPerfectTripleLeft fA fB fC
      (Fin.append (0 : Fin a → F2)
        (Fin.append x (0 : Fin c → F2))) = _
  simp [bananaPerfectTripleLeft,
    BananaMatrixStructure.directSumLinearEquiv_apply]

/-- The left action has the specified restriction to the third block. -/
theorem bananaPerfectTriple_left_third
    {a b c : ℕ}
    (fA : FinitePerfectGL a)
    (fB : FinitePerfectGL b)
    (fC : FinitePerfectGL c)
    (x : Fin c → F2) :
    (bananaPerfectTripleAutomorphism fA fB fC).left
      (Fin.append (0 : Fin a → F2)
        (Fin.append (0 : Fin b → F2) x)) =
      Fin.append (0 : Fin a → F2)
        (Fin.append (0 : Fin b → F2) (fC x)) := by
  change bananaPerfectTripleLeft fA fB fC
      (Fin.append (0 : Fin a → F2)
        (Fin.append (0 : Fin b → F2) x)) = _
  simp [bananaPerfectTripleLeft,
    BananaMatrixStructure.directSumLinearEquiv_apply]

/-- The right action on the first block is the first contragredient. -/
theorem bananaPerfectTriple_right_first
    {a b c : ℕ}
    (fA : FinitePerfectGL a)
    (fB : FinitePerfectGL b)
    (fC : FinitePerfectGL c)
    (x : Fin a → F2) :
    (bananaPerfectTripleAutomorphism fA fB fC).right
      (Fin.append x (0 : Fin (b + c) → F2)) =
      Fin.append (dotContragredient fA x)
        (0 : Fin (b + c) → F2) := by
  change dotContragredient (bananaPerfectTripleLeft fA fB fC)
      (Fin.append x (0 : Fin (b + c) → F2)) = _
  rw [bananaPerfectTripleLeft,
    BananaMatrixStructure.dotContragredient_directSumLinearEquiv]
  simp [BananaMatrixStructure.directSumLinearEquiv_apply]

/-- The right action on the second block is the second contragredient. -/
theorem bananaPerfectTriple_right_second
    {a b c : ℕ}
    (fA : FinitePerfectGL a)
    (fB : FinitePerfectGL b)
    (fC : FinitePerfectGL c)
    (x : Fin b → F2) :
    (bananaPerfectTripleAutomorphism fA fB fC).right
      (Fin.append (0 : Fin a → F2)
        (Fin.append x (0 : Fin c → F2))) =
      Fin.append (0 : Fin a → F2)
        (Fin.append (dotContragredient fB x)
          (0 : Fin c → F2)) := by
  change dotContragredient (bananaPerfectTripleLeft fA fB fC)
      (Fin.append (0 : Fin a → F2)
        (Fin.append x (0 : Fin c → F2))) = _
  rw [bananaPerfectTripleLeft,
    BananaMatrixStructure.dotContragredient_directSumLinearEquiv,
    BananaMatrixStructure.dotContragredient_directSumLinearEquiv]
  simp [BananaMatrixStructure.directSumLinearEquiv_apply]

/-- The right action on the third block is the third contragredient. -/
theorem bananaPerfectTriple_right_third
    {a b c : ℕ}
    (fA : FinitePerfectGL a)
    (fB : FinitePerfectGL b)
    (fC : FinitePerfectGL c)
    (x : Fin c → F2) :
    (bananaPerfectTripleAutomorphism fA fB fC).right
      (Fin.append (0 : Fin a → F2)
        (Fin.append (0 : Fin b → F2) x)) =
      Fin.append (0 : Fin a → F2)
        (Fin.append (0 : Fin b → F2)
          (dotContragredient fC x)) := by
  change dotContragredient (bananaPerfectTripleLeft fA fB fC)
      (Fin.append (0 : Fin a → F2)
        (Fin.append (0 : Fin b → F2) x)) = _
  rw [bananaPerfectTripleLeft,
    BananaMatrixStructure.dotContragredient_directSumLinearEquiv,
    BananaMatrixStructure.dotContragredient_directSumLinearEquiv]
  simp [BananaMatrixStructure.directSumLinearEquiv_apply]

/-- The triple automorphism preserves the full perfect pairing. -/
theorem bananaPerfectTriple_pairing
    {a b c : ℕ}
    (fA : FinitePerfectGL a)
    (fB : FinitePerfectGL b)
    (fC : FinitePerfectGL c)
    (x y : Fin (a + (b + c)) → F2) :
    (perfectBanana (a + (b + c))).eval
      ((bananaPerfectTripleAutomorphism fA fB fC).left x)
      ((bananaPerfectTripleAutomorphism fA fB fC).right y) =
    (perfectBanana (a + (b + c))).eval x y :=
  (bananaPerfectTripleAutomorphism fA fB fC).pairing_apply x y

end SuccessorTree.NonPrecompact
