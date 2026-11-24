import BANANA.NonPrecompact.BananaArbitraryAmalgamTools
import BANANA.NonPrecompact.BananaFinitePartialSystems
import BANANA.NonPrecompact.CoherentEppaPackage
import BANANA.NonPrecompact.ConjugatedCompletionAction

/-!
# Coherent EPPA for finite BANANA structures

Package the finite completion actions into a single coherent assignment
on all isomorphisms between substructures of a given finite pairing.
-/

namespace SuccessorTree.NonPrecompact

open Module

/-- A substructure is a pair of subspaces, with the ambient pairing restricted
to these subspaces. -/
structure BananaSubpair (l r : ℕ) where
  left : Submodule F2 (Fin l → F2)
  right : Submodule F2 (Fin r → F2)

/-- A partial isomorphism of a finite BANANA structure with specified domain
and range substructures. -/
structure BananaSubpair.Iso {l r : ℕ} (A : BananaMatrixStructure l r)
    (U V : BananaSubpair l r) where
  left : U.left ≃ₗ[F2] V.left
  right : U.right ≃ₗ[F2] V.right
  pairing_apply : ∀ (x : U.left) (y : U.right),
    A.eval (left x) (right y) = A.eval x y

namespace BananaSubpair

variable {l r : ℕ} {A : BananaMatrixStructure l r}
  {U V W : BananaSubpair l r}

protected def Iso.refl (A : BananaMatrixStructure l r) (U : BananaSubpair l r) :
    Iso A U U where
  left := LinearEquiv.refl F2 U.left
  right := LinearEquiv.refl F2 U.right
  pairing_apply _ _ := rfl

protected def Iso.trans (p : Iso A U V) (q : Iso A V W) : Iso A U W where
  left := p.left.trans q.left
  right := p.right.trans q.right
  pairing_apply x y := (q.pairing_apply (p.left x) (p.right y)).trans (p.pairing_apply x y)

protected def Iso.symm (p : Iso A U V) : Iso A V U where
  left := p.left.symm
  right := p.right.symm
  pairing_apply x y := by
    simpa using (p.pairing_apply (p.left.symm x) (p.right.symm y)).symm

private theorem isoExt {p q : Iso A U V}
    (hl : p.left = q.left) (hr : p.right = q.right) : p = q := by
  cases p
  cases q
  cases hl
  cases hr
  rfl

private noncomputable def coordinates (U : Submodule F2 (Fin l → F2)) :
    (Fin (finrank F2 U) → F2) ≃ₗ[F2] U :=
  LinearEquiv.ofFinrankEq _ _ (by simp [Module.finrank_fintype_fun_eq_card])

private noncomputable def coordinateModel (A : BananaMatrixStructure l r)
    (U : BananaSubpair l r) :
    BananaMatrixStructure (finrank F2 U.left) (finrank F2 U.right) :=
  bananaPairingPullback A
    (U.left.subtype.comp (coordinates U.left).toLinearMap)
    (U.right.subtype.comp (coordinates U.right).toLinearMap)

private noncomputable def coordinateInclusion (A : BananaMatrixStructure l r)
    (U : BananaSubpair l r) : BananaMatrixEmbedding (coordinateModel A U) A where
  left := U.left.subtype.comp (coordinates U.left).toLinearMap
  right := U.right.subtype.comp (coordinates U.right).toLinearMap
  left_injective := U.left.injective_subtype.comp (coordinates U.left).injective
  right_injective := U.right.injective_subtype.comp (coordinates U.right).injective
  pairing_apply x y := (bananaPairingPullback_eval A _ _ x y).symm

private noncomputable def coordinateImage (p : Iso A U V) :
    BananaMatrixEmbedding (coordinateModel A U) A where
  left := V.left.subtype.comp (p.left.toLinearMap.comp (coordinates U.left).toLinearMap)
  right := V.right.subtype.comp (p.right.toLinearMap.comp (coordinates U.right).toLinearMap)
  left_injective := V.left.injective_subtype.comp (p.left.injective.comp (coordinates U.left).injective)
  right_injective := V.right.injective_subtype.comp (p.right.injective.comp (coordinates U.right).injective)
  pairing_apply x y := by
    calc
      _ = A.eval (coordinateInclusion A U |>.left x)
          (coordinateInclusion A U |>.right y) :=
        p.pairing_apply (coordinates U.left x) (coordinates U.right y)
      _ = _ := (coordinateInclusion A U).pairing_apply x y

private abbrev PerfectAut (n : ℕ) :=
  BananaMatrixEmbedding (perfectBanana n) (perfectBanana n)

private theorem autExt {n : ℕ} {g h : PerfectAut n}
    (hl : ∀ x, g.left x = h.left x) (hr : ∀ y, g.right y = h.right y) :
    g = h := by
  have hl' := LinearMap.ext hl
  have hr' := LinearMap.ext hr
  cases g
  cases h
  cases hl'
  cases hr'
  rfl

private theorem exists_iso_extension {n : ℕ}
    (j : BananaMatrixEmbedding A (perfectBanana n)) (p : Iso A U V) :
    ∃ g : PerfectAut n,
      (∀ x : U.left, g.left (j.left x) = j.left (p.left x)) ∧
      (∀ y : U.right, g.right (j.right y) = j.right (p.right y)) := by
  obtain ⟨g, hgL, hgR⟩ := exists_perfectPairAutomorphism_extends
    (j.comp (coordinateInclusion A U)) (j.comp (coordinateImage p))
  refine ⟨g, ?_, ?_⟩
  · intro x
    obtain ⟨z, rfl⟩ := (coordinates U.left).surjective x
    exact hgL z
  · intro y
    obtain ⟨z, rfl⟩ := (coordinates U.right).surjective y
    exact hgR z

private noncomputable def coordAut {n : ℕ} (U : Submodule F2 (Fin n → F2))
    (p : U ≃ₗ[F2] U) :
    (Fin (finrank F2 U) → F2) ≃ₗ[F2] (Fin (finrank F2 U) → F2) :=
  ((coordinates U).trans p).trans (coordinates U).symm

@[simp] private theorem coordAut_apply {n : ℕ} (U : Submodule F2 (Fin n → F2))
    (p : U ≃ₗ[F2] U) (x : Fin (finrank F2 U) → F2) :
    coordinates U (coordAut U p x) = p (coordinates U x) := by
  simp [coordAut]

private theorem coordAut_trans {n : ℕ} (U : Submodule F2 (Fin n → F2))
    (p q : U ≃ₗ[F2] U) :
    coordAut U (p.trans q) = (coordAut U p).trans (coordAut U q) := by
  apply LinearEquiv.ext
  intro x
  apply (coordinates U).injective
  simp

private theorem coordAut_refl {n : ℕ} (U : Submodule F2 (Fin n → F2)) :
    coordAut U (LinearEquiv.refl F2 U) = LinearEquiv.refl F2 _ := by
  apply LinearEquiv.ext
  intro x
  apply (coordinates U).injective
  simp

private theorem exists_local_action {n : ℕ}
    (j : BananaMatrixEmbedding A (perfectBanana n)) (U : BananaSubpair l r)
    (hn : finrank F2 U.left + finrank F2 U.right ≤ n) :
    ∃ rho : Iso A U U → PerfectAut n,
      (∀ (p : Iso A U U) (x : U.left), (rho p).left (j.left x) = j.left (p.left x)) ∧
      (∀ (p : Iso A U U) (y : U.right), (rho p).right (j.right y) = j.right (p.right y)) ∧
      rho (Iso.refl A U) = BananaMatrixEmbedding.id _ ∧
      (∀ p q, rho (p.trans q) = (rho q).comp (rho p)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨E, _, _, hExt, hIdL, hIdR, hCompL, hCompR⟩ :=
    (coordinateModel A U).exists_alignedCoherentAmbientAction
      (j.comp (coordinateInclusion A U)) (BananaMatrixStructure.standardPerfectBlockEmbedding _ k)
  let rho (p : Iso A U U) :=
    BananaMatrixStructure.embeddedCompletionAmbientAutomorphism E
      (coordAut U.left p.left) (coordAut U.right p.right)
  have hPair (p : Iso A U U) :
      ∀ x y, (coordinateModel A U).eval (coordAut U.left p.left x)
        (coordAut U.right p.right y) = (coordinateModel A U).eval x y := by
    intro x y
    rw [← (coordinateInclusion A U).pairing_apply,
      ← (coordinateInclusion A U).pairing_apply x y]
    change A.eval (coordinates U.left (coordAut U.left p.left x))
      (coordinates U.right (coordAut U.right p.right y)) = _
    rw [coordAut_apply, coordAut_apply]
    exact p.pairing_apply _ _
  refine ⟨rho, ?_, ?_, ?_, ?_⟩
  · intro p x
    obtain ⟨z, rfl⟩ := (coordinates U.left).surjective x
    have h := (hExt _ _ (hPair p)).1 z
    change (rho p).left (j.left (coordinates U.left z)) =
      j.left ↑(coordinates U.left (coordAut U.left p.left z)) at h
    simpa only [coordAut_apply] using h
  · intro p y
    obtain ⟨z, rfl⟩ := (coordinates U.right).surjective y
    have h := (hExt _ _ (hPair p)).2 z
    change (rho p).right (j.right (coordinates U.right z)) =
      j.right ↑(coordinates U.right (coordAut U.right p.right z)) at h
    simpa only [coordAut_apply] using h
  · apply autExt
    · intro x
      simpa [rho, Iso.refl, coordAut_refl, BananaMatrixEmbedding.id] using
        LinearMap.congr_fun hIdL x
    · intro y
      simpa [rho, Iso.refl, coordAut_refl, BananaMatrixEmbedding.id] using
        LinearMap.congr_fun hIdR y
  · intro p q
    apply autExt
    · intro x
      simpa [rho, Iso.trans, coordAut_trans] using
        LinearMap.congr_fun (hCompL _ _ _ _) x
    · intro y
      simpa [rho, Iso.trans, coordAut_trans] using
        LinearMap.congr_fun (hCompR _ _ _ _) y

private def isoSetoid (A : BananaMatrixStructure l r) : Setoid (BananaSubpair l r) where
  r U V := Nonempty (Iso A U V)
  iseqv := ⟨fun U => ⟨Iso.refl A U⟩, fun ⟨p⟩ => ⟨p.symm⟩, fun ⟨p⟩ ⟨q⟩ => ⟨p.trans q⟩⟩

private abbrev isoClass (A : BananaMatrixStructure l r) (U : BananaSubpair l r) :=
  @Quotient.mk _ (isoSetoid A) U

private theorem isoClass_eq (p : Iso A U V) : isoClass A U = isoClass A V :=
  Quotient.sound (show Nonempty (Iso A U V) from ⟨p⟩)

private noncomputable def chart {C : Quotient (isoSetoid A)}
    (hU : isoClass A U = C) : Iso A C.out U :=
  Classical.choice (Quotient.exact ((Quotient.out_eq C).trans hU.symm) :
    Nonempty (Iso A C.out U))

private noncomputable def chartExtension {n : ℕ} (j : BananaMatrixEmbedding A (perfectBanana n))
    {C : Quotient (isoSetoid A)} (hU : isoClass A U = C) : PerfectAut n :=
  Classical.choose (exists_iso_extension j (chart hU))

@[simp] private theorem chartExtension_left {n : ℕ}
    (j : BananaMatrixEmbedding A (perfectBanana n)) {C : Quotient (isoSetoid A)}
    (hU : isoClass A U = C) (x : C.out.left) :
    (chartExtension j hU).left (j.left x) = j.left ((chart hU).left x) :=
  (Classical.choose_spec (exists_iso_extension j (chart hU))).1 x

@[simp] private theorem chartExtension_right {n : ℕ}
    (j : BananaMatrixEmbedding A (perfectBanana n)) {C : Quotient (isoSetoid A)}
    (hU : isoClass A U = C) (y : C.out.right) :
    (chartExtension j hU).right (j.right y) = j.right ((chart hU).right y) :=
  (Classical.choose_spec (exists_iso_extension j (chart hU))).2 y

private abbrev WitnessAut (l r : ℕ) := PerfectAut (l + r)

private theorem local_action_for_completion (A : BananaMatrixStructure l r)
    (U : BananaSubpair l r) :
    ∃ rho : Iso A U U → WitnessAut l r,
      (∀ (p : Iso A U U) (x : U.left),
        (rho p).left (A.completionLeft x) = A.completionLeft (p.left x)) ∧
      (∀ (p : Iso A U U) (y : U.right),
        (rho p).right (A.completionRight y) = A.completionRight (p.right y)) ∧
      rho (Iso.refl A U) = BananaMatrixEmbedding.id _ ∧
      (∀ p q, rho (p.trans q) = (rho q).comp (rho p)) := by
  apply exists_local_action A.completionEmbedding
  have hL : finrank F2 U.left ≤ l := by
    simpa [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le U.left
  have hR : finrank F2 U.right ≤ r := by
    simpa [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le U.right
  exact Nat.add_le_add hL hR

private noncomputable def rho (C : Quotient (isoSetoid A)) :
    Iso A C.out C.out → WitnessAut l r :=
  Classical.choose (local_action_for_completion A C.out)

private theorem rho_left (C : Quotient (isoSetoid A))
    (p : Iso A C.out C.out) (x : C.out.left) :
    (rho C p).left (A.completionLeft x) = A.completionLeft (p.left x) :=
  (Classical.choose_spec (local_action_for_completion A C.out)).1 p x

private theorem rho_right (C : Quotient (isoSetoid A))
    (p : Iso A C.out C.out) (y : C.out.right) :
    (rho C p).right (A.completionRight y) = A.completionRight (p.right y) :=
  (Classical.choose_spec (local_action_for_completion A C.out)).2.1 p y

private theorem rho_refl (C : Quotient (isoSetoid A)) :
    rho C (Iso.refl A C.out) = BananaMatrixEmbedding.id _ :=
  (Classical.choose_spec (local_action_for_completion A C.out)).2.2.1

private theorem rho_trans (C : Quotient (isoSetoid A))
    (p q : Iso A C.out C.out) : rho C (p.trans q) = (rho C q).comp (rho C p) :=
  (Classical.choose_spec (local_action_for_completion A C.out)).2.2.2 p q

private noncomputable def inChart {C : Quotient (isoSetoid A)}
    (hU : isoClass A U = C) (hV : isoClass A V = C) (p : Iso A U V) :
    Iso A C.out C.out :=
  ((chart hU).trans p).trans (chart hV).symm

private theorem inChart_refl {C : Quotient (isoSetoid A)}
    (hU : isoClass A U = C) : inChart hU hU (Iso.refl A U) = Iso.refl A C.out := by
  apply isoExt <;> apply LinearEquiv.ext <;> intro x <;>
    simp [inChart, Iso.trans, Iso.refl, Iso.symm]

private theorem inChart_trans {C : Quotient (isoSetoid A)}
    (hU : isoClass A U = C) (hV : isoClass A V = C) (hW : isoClass A W = C)
    (p : Iso A U V) (q : Iso A V W) :
    inChart hU hW (p.trans q) = (inChart hU hV p).trans (inChart hV hW q) := by
  apply isoExt <;> apply LinearEquiv.ext <;> intro x <;>
    simp [inChart, Iso.trans, Iso.symm]

private noncomputable def extendInClass {C : Quotient (isoSetoid A)}
    (hU : isoClass A U = C) (hV : isoClass A V = C) (p : Iso A U V) : WitnessAut l r :=
  (chartExtension A.completionEmbedding hV).comp
    ((rho C (inChart hU hV p)).comp
      (chartExtension A.completionEmbedding hU).inversePerfectSelfEmbedding)

private theorem extendInClass_left {C : Quotient (isoSetoid A)}
    (hU : isoClass A U = C) (hV : isoClass A V = C) (p : Iso A U V) (x : U.left) :
    (extendInClass hU hV p).left (A.completionLeft x) = A.completionLeft (p.left x) := by
  let g := chartExtension A.completionEmbedding hU
  let h := chartExtension A.completionEmbedding hV
  let z := (chart hU).left.symm x
  have hx : g.left (A.completionLeft z) = A.completionLeft x := by
    simpa [g, z, BananaMatrixStructure.completionEmbedding] using
      chartExtension_left A.completionEmbedding hU z
  change h.left ((rho C (inChart hU hV p)).left
    (g.inversePerfectSelfEmbedding.left (A.completionLeft x))) = _
  rw [← hx, BananaMatrixEmbedding.inversePerfectSelfEmbedding_left_comp, rho_left]
  change (chartExtension A.completionEmbedding hV).left
    (A.completionEmbedding.left ((inChart hU hV p).left z)) = _
  rw [chartExtension_left]
  simp [inChart, Iso.trans, Iso.symm, z, BananaMatrixStructure.completionEmbedding]

private theorem extendInClass_right {C : Quotient (isoSetoid A)}
    (hU : isoClass A U = C) (hV : isoClass A V = C) (p : Iso A U V) (y : U.right) :
    (extendInClass hU hV p).right (A.completionRight y) = A.completionRight (p.right y) := by
  let g := chartExtension A.completionEmbedding hU
  let h := chartExtension A.completionEmbedding hV
  let z := (chart hU).right.symm y
  have hy : g.right (A.completionRight z) = A.completionRight y := by
    simpa [g, z, BananaMatrixStructure.completionEmbedding] using
      chartExtension_right A.completionEmbedding hU z
  change h.right ((rho C (inChart hU hV p)).right
    (g.inversePerfectSelfEmbedding.right (A.completionRight y))) = _
  rw [← hy, BananaMatrixEmbedding.inversePerfectSelfEmbedding_right_comp, rho_right]
  change (chartExtension A.completionEmbedding hV).right
    (A.completionEmbedding.right ((inChart hU hV p).right z)) = _
  rw [chartExtension_right]
  simp [inChart, Iso.trans, Iso.symm, z, BananaMatrixStructure.completionEmbedding]

private theorem extendInClass_refl {C : Quotient (isoSetoid A)}
    (hU : isoClass A U = C) :
    extendInClass hU hU (Iso.refl A U) = BananaMatrixEmbedding.id _ := by
  unfold extendInClass
  rw [inChart_refl, rho_refl]
  apply autExt
  · intro x
    exact BananaMatrixEmbedding.inversePerfectSelfEmbedding_left_rightInverse _ x
  · intro y
    exact BananaMatrixEmbedding.inversePerfectSelfEmbedding_right_rightInverse _ y

private theorem extendInClass_trans {C : Quotient (isoSetoid A)}
    (hU : isoClass A U = C) (hV : isoClass A V = C) (hW : isoClass A W = C)
    (p : Iso A U V) (q : Iso A V W) :
    extendInClass hU hW (p.trans q) =
      (extendInClass hV hW q).comp (extendInClass hU hV p) := by
  unfold extendInClass
  rw [inChart_trans hU hV hW, rho_trans]
  apply autExt
  · intro x
    simp only [BananaMatrixEmbedding.comp, LinearMap.comp_apply,
      BananaMatrixEmbedding.inversePerfectSelfEmbedding_left_comp]
  · intro y
    simp only [BananaMatrixEmbedding.comp, LinearMap.comp_apply,
      BananaMatrixEmbedding.inversePerfectSelfEmbedding_right_comp]

private noncomputable def extend (p : Iso A U V) : WitnessAut l r :=
  extendInClass (C := isoClass A U) rfl (isoClass_eq p).symm p

private theorem extend_eq_extendInClass {C : Quotient (isoSetoid A)}
    (hU : isoClass A U = C) (hV : isoClass A V = C) (p : Iso A U V) :
    extend p = extendInClass hU hV p := by
  subst C
  rfl

end BananaSubpair

namespace BananaMatrixStructure

open BananaSubpair

/-- The canonical perfect completion of a finite BANANA structure gives
one coherent EPPA witness for all its partial isomorphisms. Both sorts
of the witness have dimension l+r. -/
theorem exists_coherentEppaWitness {l r : ℕ} (A : BananaMatrixStructure l r) :
    ∃ Θ : ∀ U V : BananaSubpair l r, BananaSubpair.Iso A U V →
        BananaMatrixEmbedding (perfectBanana (l + r)) (perfectBanana (l + r)),
      (∀ U V (p : BananaSubpair.Iso A U V) (x : U.left),
        (Θ U V p).left (A.completionLeft x) = A.completionLeft (p.left x)) ∧
      (∀ U V (p : BananaSubpair.Iso A U V) (y : U.right),
        (Θ U V p).right (A.completionRight y) = A.completionRight (p.right y)) ∧
      (∀ U, Θ U U (BananaSubpair.Iso.refl A U) = BananaMatrixEmbedding.id _) ∧
      (∀ U V W (p : BananaSubpair.Iso A U V) (q : BananaSubpair.Iso A V W),
        Θ U W (p.trans q) = (Θ V W q).comp (Θ U V p)) := by
  refine ⟨fun _ _ p => extend p, ?_, ?_, ?_, ?_⟩
  · intro U V p x
    exact extendInClass_left _ _ p x
  · intro U V p y
    exact extendInClass_right _ _ p y
  · intro U
    exact extendInClass_refl rfl
  · intro U V W p q
    have hV := (isoClass_eq p).symm
    have hW := (isoClass_eq q).symm.trans hV
    change extend (p.trans q) = (extend q).comp (extend p)
    rw [extend_eq_extendInClass rfl hW, extend_eq_extendInClass hV hW,
      extend_eq_extendInClass rfl hV]
    exact extendInClass_trans rfl hV hW p q

end BananaMatrixStructure

end SuccessorTree.NonPrecompact
