import BANANA.NonPrecompact.PrebananaFiniteBridgeGlobalAutomorphism
import BANANA.NonPrecompact.BooleanBananaStoneAction
import Mathlib.Data.Fintype.Prod

/-!
# Proper zero-marked elements of a marked Boolean limit

The marked algebra on two atoms, both marked zero, embeds by sending its
atoms to a proper nonzero zero-marked element and its complement. The
finite extension property makes any two such embeddings conjugate.
-/

namespace SuccessorTree.NonPrecompact.BooleanBanana

private abbrev twoZeroMarkedAtoms : PrebananaFiniteBooleanModel where
  carrier := Bool × Bool
  μ := fun _ => 0
  μ_bot := rfl
  μ_top := rfl
  μ_add := fun _ _ _ => by simp

private def selectAtom {B : Type*} [Bot B] (x : B) : Bool → B
  | false => ⊥
  | true => x

private theorem selectAtom_injective {B : Type*} [Bot B] {x : B} (hx : x ≠ ⊥) :
    Function.Injective (selectAtom x) := by
  intro u v h
  cases u <;> cases v
  · rfl
  · exact (hx h.symm).elim
  · exact (hx h).elim
  · rfl

private def twoAtomMap {B : Type*} [BooleanAlgebra B] (x : B) (b : Bool × Bool) : B :=
  selectAtom x b.1 ⊔ selectAtom xᶜ b.2

private theorem selectAtom_sup {B : Type*} [BooleanAlgebra B] (x : B) (a b : Bool) :
    selectAtom x (a ⊔ b) = selectAtom x a ⊔ selectAtom x b := by
  simp only [Bool.sup_eq_bor]
  cases a <;> cases b <;> simp [selectAtom]

private theorem selectAtom_inf {B : Type*} [BooleanAlgebra B] (x : B) (a b : Bool) :
    selectAtom x (a ⊓ b) = selectAtom x a ⊓ selectAtom x b := by
  simp only [Bool.inf_eq_band]
  cases a <;> cases b <;> simp [selectAtom]

private theorem selectAtom_inf_compl {B : Type*} [BooleanAlgebra B] (x : B) (a b : Bool) :
    selectAtom x a ⊓ selectAtom xᶜ b = ⊥ := by
  cases a <;> cases b <;> simp [selectAtom]

private theorem twoAtomMap_inf_first {B : Type*} [BooleanAlgebra B]
    (x : B) (b : Bool × Bool) : twoAtomMap x b ⊓ x = selectAtom x b.1 := by
  obtain ⟨(_ | _), (_ | _)⟩ := b <;> simp [twoAtomMap, selectAtom]

private theorem twoAtomMap_inf_second {B : Type*} [BooleanAlgebra B]
    (x : B) (b : Bool × Bool) : twoAtomMap x b ⊓ xᶜ = selectAtom xᶜ b.2 := by
  obtain ⟨(_ | _), (_ | _)⟩ := b <;> simp [twoAtomMap, selectAtom]

private def twoZeroMarkedEmbedding (M : PrebananaCountableBooleanModel)
    (x : M.carrier) (hbot : x ≠ ⊥) (htop : x ≠ ⊤) (hmark : M.μ x = 0) :
    PrebananaFiniteToCountableEmbedding twoZeroMarkedAtoms M where
  hom := {
    toFun := twoAtomMap x
    map_bot' := by
      change twoAtomMap x (false, false) = ⊥
      simp [twoAtomMap, selectAtom]
    map_top' := by
      change twoAtomMap x (true, true) = ⊤
      simp [twoAtomMap, selectAtom]
    map_sup' := by
      intro a b
      change selectAtom x (a.1 ⊔ b.1) ⊔ selectAtom xᶜ (a.2 ⊔ b.2) =
        (selectAtom x a.1 ⊔ selectAtom xᶜ a.2) ⊔ (selectAtom x b.1 ⊔ selectAtom xᶜ b.2)
      rw [selectAtom_sup, selectAtom_sup, sup_sup_sup_comm]
    map_inf' := by
      intro a b
      change selectAtom x (a.1 ⊓ b.1) ⊔ selectAtom xᶜ (a.2 ⊓ b.2) =
        (selectAtom x a.1 ⊔ selectAtom xᶜ a.2) ⊓ (selectAtom x b.1 ⊔ selectAtom xᶜ b.2)
      have hcross : selectAtom xᶜ a.2 ⊓ selectAtom x b.1 = ⊥ :=
        (inf_comm _ _).trans (selectAtom_inf_compl x b.1 a.2)
      rw [selectAtom_inf, selectAtom_inf, inf_sup_right, inf_sup_left, inf_sup_left,
        selectAtom_inf_compl x a.1 b.2, hcross, sup_bot_eq, bot_sup_eq]
  }
  injective := by
    intro a b hab
    change twoAtomMap x a = twoAtomMap x b at hab
    apply Prod.ext
    · exact selectAtom_injective hbot ((twoAtomMap_inf_first x a).symm.trans
        ((congrArg (· ⊓ x) hab).trans (twoAtomMap_inf_first x b)))
    · exact selectAtom_injective (fun h => htop (compl_eq_bot.mp h))
        ((twoAtomMap_inf_second x a).symm.trans
          ((congrArg (· ⊓ xᶜ) hab).trans (twoAtomMap_inf_second x b)))
  preserves_μ := by
    change ∀ a : Bool × Bool, M.μ (twoAtomMap x a) = 0
    have hcompl : M.μ xᶜ = 0 := by
      have ha := M.μ_add x xᶜ (inf_compl_eq_bot : x ⊓ xᶜ = ⊥)
      simpa [hmark, M.μ_top] using ha.symm
    rintro ⟨(_ | _), (_ | _)⟩ <;>
      simp [twoAtomMap, selectAtom, M.μ_bot, M.μ_top, hmark, hcompl]

/-- Any two proper nonzero zero-marked elements are conjugate under the
actual marked automorphism group of a countable marked Boolean limit. -/
theorem properZeroMark_transitive_of_finiteExtension
    {M : PrebananaCountableBooleanModel}
    (hfinite : M.HasFiniteAmbients) (hext : M.HasFiniteExtensionProperty)
    {x y : M.carrier}
    (hxbot : x ≠ ⊥) (hxtop : x ≠ ⊤) (hxmark : M.μ x = 0)
    (hybot : y ≠ ⊥) (hytop : y ≠ ⊤) (hymark : M.μ y = 0) :
    ∃ g : markedAutomorphisms M.μ, g • x = y := by
  let p : PrebananaFiniteBridge M :=
    ⟨twoZeroMarkedAtoms, twoZeroMarkedEmbedding M x hxbot hxtop hxmark,
      twoZeroMarkedEmbedding M y hybot hytop hymark⟩
  obtain ⟨E, hmark, hE⟩ := p.exists_global_marked_automorphism hfinite hext
  refine ⟨ofMarkedOrderIso E hmark, ?_⟩
  change E x = y
  have h := hE (true, false)
  change E (twoAtomMap x (true, false)) = twoAtomMap y (true, false) at h
  simpa [twoAtomMap, selectAtom] using h

end SuccessorTree.NonPrecompact.BooleanBanana
