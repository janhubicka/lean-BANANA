import BANANA.NonPrecompact.BananaMatrixRepresentativeIso
import BANANA.NonPrecompact.CoherentConjugation

/-!
# Coherent transport for actual BANANA isomorphisms

Once a representative, its extending group homomorphism, and one aligned
ambient conjugator for each object have been chosen, the construction below
assigns an ambient automorphism to EVERY isomorphism between these objects.
It extends the isomorphism on both sorts and respects identity, composition
and inverse. No action of arbitrary carrier permutations is assumed.

These hypotheses must still be constructed for all isomorphism classes of
substructures of a fixed finite A in the same dimension-bounded witness.
-/

namespace SuccessorTree.NonPrecompact

section Transport

variable {O : Type*} {l r a b : ℕ} {dL dR : O → ℕ}
variable {A : BananaMatrixStructure l r}
variable {B : ∀ U : O, BananaMatrixStructure (dL U) (dR U)}
variable {C : BananaMatrixStructure a b}

/-- Conjugate the actual representative automorphism in a common witness. -/
def bananaMatrixCoherentTransport
    (rho : BananaMatrixAutGroup A →* BananaMatrixAutGroup C)
    (g : O → BananaMatrixAutGroup C)
    (i : ∀ U, BananaMatrixIso A (B U)) {U V : O}
    (p : BananaMatrixIso (B U) (B V)) : BananaMatrixAutGroup C :=
  conjugatedTransport rho g U V (bananaMatrixRepresentativeCode i p)

/-- Identity on any selected object is sent to the ambient identity. -/
theorem bananaMatrixCoherentTransport_refl
    (rho : BananaMatrixAutGroup A →* BananaMatrixAutGroup C)
    (g : O → BananaMatrixAutGroup C)
    (i : ∀ U, BananaMatrixIso A (B U)) (U : O) :
    bananaMatrixCoherentTransport rho g i (BananaMatrixIso.refl (B U)) = 1 := by
  unfold bananaMatrixCoherentTransport
  rw [bananaMatrixRepresentativeCode_refl, conjugatedTransport_one]

/-- All composable isomorphisms are extended coherently, not chosen afresh. -/
theorem bananaMatrixCoherentTransport_trans
    (rho : BananaMatrixAutGroup A →* BananaMatrixAutGroup C)
    (g : O → BananaMatrixAutGroup C)
    (i : ∀ U, BananaMatrixIso A (B U)) {U V W : O}
    (p : BananaMatrixIso (B U) (B V)) (q : BananaMatrixIso (B V) (B W)) :
    bananaMatrixCoherentTransport rho g i q *
        bananaMatrixCoherentTransport rho g i p =
      bananaMatrixCoherentTransport rho g i (p.trans q) := by
  unfold bananaMatrixCoherentTransport
  rw [bananaMatrixRepresentativeCode_trans]
  exact conjugatedTransport_mul rho g U V W
    (bananaMatrixRepresentativeCode i p) (bananaMatrixRepresentativeCode i q)

/-- Inverse coherence holds in the actual ambient automorphism group. -/
theorem bananaMatrixCoherentTransport_symm
    (rho : BananaMatrixAutGroup A →* BananaMatrixAutGroup C)
    (g : O → BananaMatrixAutGroup C)
    (i : ∀ U, BananaMatrixIso A (B U)) {U V : O}
    (p : BananaMatrixIso (B U) (B V)) :
    (bananaMatrixCoherentTransport rho g i p)⁻¹ =
      bananaMatrixCoherentTransport rho g i p.symm := by
  unfold bananaMatrixCoherentTransport
  rw [bananaMatrixRepresentativeCode_symm]
  exact conjugatedTransport_inv rho g U V (bananaMatrixRepresentativeCode i p)

/-- Extension on both sorts for all arrows between the selected copies.
The homomorphism and each conjugator must agree on BOTH sorts. -/
theorem bananaMatrixCoherentTransport_extends
    (rho : BananaMatrixAutGroup A →* BananaMatrixAutGroup C)
    (g : O → BananaMatrixAutGroup C)
    (i : ∀ U, BananaMatrixIso A (B U))
    (j₀ : BananaMatrixEmbedding A C)
    (j : ∀ U, BananaMatrixEmbedding (B U) C)
    (hρL : ∀ (h : BananaMatrixAutGroup A) x,
      (rho h).1.1 (j₀.left x) = j₀.left (h.1.1 x))
    (hρR : ∀ (h : BananaMatrixAutGroup A) y,
      (rho h).1.2 (j₀.right y) = j₀.right (h.1.2 y))
    (hgL : ∀ U x, (g U).1.1 (j₀.left x) = (j U).left ((i U).left x))
    (hgR : ∀ U y, (g U).1.2 (j₀.right y) = (j U).right ((i U).right y))
    {U V : O} (p : BananaMatrixIso (B U) (B V)) :
    (∀ x, (bananaMatrixCoherentTransport rho g i p).1.1 ((j U).left x) =
      (j V).left (p.left x)) ∧
    (∀ y, (bananaMatrixCoherentTransport rho g i p).1.2 ((j U).right y) =
      (j V).right (p.right y)) := by
  constructor
  · intro x
    obtain ⟨x, rfl⟩ := (i U).left.surjective x
    calc
      (bananaMatrixCoherentTransport rho g i p).1.1
          ((j U).left ((i U).left x)) =
          (g V).1.1 ((rho (bananaMatrixRepresentativeCode i p)).1.1 (j₀.left x)) := by
        rw [← hgL U x]
        change (g V).1.1 ((rho (bananaMatrixRepresentativeCode i p)).1.1
          ((g U).1.1.symm ((g U).1.1 (j₀.left x)))) = _
        rw [LinearEquiv.symm_apply_apply]
      _ = (g V).1.1 (j₀.left ((bananaMatrixRepresentativeCode i p).1.1 x)) := by
        rw [hρL]
      _ = (j V).left ((i V).left ((bananaMatrixRepresentativeCode i p).1.1 x)) :=
        hgL V _
      _ = (j V).left (p.left ((i U).left x)) := by
        rw [bananaMatrixRepresentativeCode_left]
  · intro y
    obtain ⟨y, rfl⟩ := (i U).right.surjective y
    calc
      (bananaMatrixCoherentTransport rho g i p).1.2
          ((j U).right ((i U).right y)) =
          (g V).1.2 ((rho (bananaMatrixRepresentativeCode i p)).1.2 (j₀.right y)) := by
        rw [← hgR U y]
        change (g V).1.2 ((rho (bananaMatrixRepresentativeCode i p)).1.2
          ((g U).1.2.symm ((g U).1.2 (j₀.right y)))) = _
        rw [LinearEquiv.symm_apply_apply]
      _ = (g V).1.2 (j₀.right ((bananaMatrixRepresentativeCode i p).1.2 y)) := by
        rw [hρR]
      _ = (j V).right ((i V).right ((bananaMatrixRepresentativeCode i p).1.2 y)) :=
        hgR V _
      _ = (j V).right (p.right ((i U).right y)) := by
        rw [bananaMatrixRepresentativeCode_right]

end Transport

end SuccessorTree.NonPrecompact
