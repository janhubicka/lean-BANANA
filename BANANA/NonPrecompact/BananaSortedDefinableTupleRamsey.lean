import BANANA.NonPrecompact.BananaTaggedSyntaxReverse
import BANANA.NonPrecompact.BananaLimitDefinableColouring

/-!
# Definable tuple Ramsey in the sorted BANANA language

Unary tags recover the sorts of the monochromatic target tuple. The
two-way translation identifies the eligible source copies and transports
the truth values of the colour formulas with the parameters held fixed.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder
open scoped FirstOrder

universe u v w w'

private theorem hasDefinableTupleRamsey_of_equiv {L : Language.{u, v}}
    {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N] (e : M ≃[L] N)
    (h : HasDefinableTupleRamsey L N) : HasDefinableTupleRamsey L M := by
  intro l r k c a b p φ
  have realizes {α : Type} (ψ : L.Formula α) (x : α → M) :
      ψ.Realize (e ∘ x) ↔ ψ.Realize x :=
    Language.StrongHomClass.realize_formula e ψ
  obtain ⟨d, hd, hmono⟩ := h (e ∘ a) (e ∘ b) (e ∘ p) φ
  have ed : e ∘ (e.symm ∘ d) = d :=
    funext fun i => e.apply_symm_apply (d i)
  refine ⟨e.symm ∘ d, ?_, ?_⟩
  · intro ψ
    calc
      ψ.Realize b ↔ ψ.Realize (e ∘ b) := (realizes ψ b).symm
      _ ↔ ψ.Realize d := hd ψ
      _ ↔ ψ.Realize (e.symm ∘ d) := by
        have hh := realizes ψ (e.symm ∘ d)
        rw [ed] at hh
        exact hh
  · intro i j hi hj t
    have type (i : Fin l → Fin r) (hi : SameFormulaType (L := L) a (b ∘ i)) :
        SameFormulaType (L := L) (e ∘ a) ((e ∘ b) ∘ i) :=
      fun ψ => (realizes ψ a).trans ((hi ψ).trans (realizes ψ (b ∘ i)).symm)
    have color (i : Fin l → Fin r) :
        (φ t).Realize (Sum.elim (d ∘ i) (e ∘ p)) ↔
        (φ t).Realize (Sum.elim ((e.symm ∘ d) ∘ i) p) := by
      rw [← show e ∘ Sum.elim ((e.symm ∘ d) ∘ i) p = Sum.elim (d ∘ i) (e ∘ p) from
        funext fun z => by cases z with
          | inl x => exact e.apply_symm_apply (d (i x))
          | inr x => rfl]
      exact realizes (φ t) _
    exact (color i).symm.trans ((hmono i j (type i hi) (type j hj) t).trans (color j))

namespace BananaSorted

variable {V : BananaSort → Type v}

/-- A choice of target coordinates of the indicated source sorts.
Repeated coordinates are allowed. -/
abbrev CompatibleIndices {l r : ℕ} (source : Fin l → BananaSort)
    (target : Fin r → BananaSort) :=
  { i : Fin l → Fin r // ∀ j, target (i j) = source j }

/-- Select coordinates along a map preserving sorts. -/
def restrictTuple {l r : ℕ} {source : Fin l → BananaSort} {target : Fin r → BananaSort}
    (i : CompatibleIndices source target) (b : ∀ j, V (target j)) (j : Fin l) :
    V (source j) :=
  cast (congrArg V (i.property j)) (b (i.val j))

/-- Put tuple coordinates and parameters in a single sorted assignment. -/
def sumTuple {α β : Type*} {s : α → BananaSort} {t : β → BananaSort}
    (x : ∀ a, V (s a)) (y : ∀ b, V (t b)) : ∀ j, V (Sum.elim s t j)
  | .inl a => x a
  | .inr b => y b

private theorem tag_cast_sort {s t : BananaSort} (h : s = t) (x : V s) :
    tag (V := V) (cast (congrArg V h) x) = tag x := by
  cases h
  rfl

private theorem tag_restrictTuple {l r : ℕ} {s : Fin l → BananaSort} {t : Fin r → BananaSort}
    (u : CompatibleIndices s t) (b : ∀ i, V (t i)) :
    (fun j => tag (restrictTuple u b j)) = (fun j => tag (b j)) ∘ u.val :=
  funext fun j => tag_cast_sort (u.property j) (b (u.val j))

private theorem tag_sumTuple {α β : Type*} {s : α → BananaSort} {t : β → BananaSort}
    (x : ∀ a, V (s a)) (y : ∀ b, V (t b)) :
    (fun j => tag (sumTuple x y j)) = Sum.elim (fun j => tag (x j)) (fun j => tag (y j)) := by
  funext j
  cases j <;> rfl

variable [∀ s, Zero (V s)] [∀ s, Add (V s)]

/-- Tuples of the same sort profile agree on all sorted formulas, with
the auxiliary variable stock assigned zero. -/
def SameSortedFormulaType {n : ℕ} {profile : Fin n → BananaSort}
    (pair : V .left → V .right → F2) (a b : ∀ j, V (profile j)) : Prop :=
  ∀ φ : Formula (syntaxSort profile), φ.realize pair (zeroExtend a) ↔
    φ.realize pair (zeroExtend b)

/-- The definable elementary embedding Ramsey property for sorted tuples
and colour formulas in the two-sorted BANANA language. -/
def HasSortedDefinableTupleRamsey (pair : V .left → V .right → F2) : Prop :=
  ∀ {l r k c : ℕ} (aSort : Fin l → BananaSort) (bSort : Fin r → BananaSort)
    (pSort : Fin k → BananaSort) (a : ∀ j, V (aSort j)) (b : ∀ j, V (bSort j))
    (p : ∀ j, V (pSort j)) (φ : Fin c → Formula (syntaxSort (Sum.elim aSort pSort))),
    ∃ d : ∀ j, V (bSort j), SameSortedFormulaType pair b d ∧
      ∀ (i j : CompatibleIndices aSort bSort),
        SameSortedFormulaType pair a (restrictTuple i b) →
        SameSortedFormulaType pair a (restrictTuple j b) →
        ∀ t, (φ t).realize pair (zeroExtend (sumTuple (restrictTuple i d) p)) ↔
          (φ t).realize pair (zeroExtend (sumTuple (restrictTuple j d) p))

private theorem exists_tag_eq_of_sameFormulaType {n : ℕ} {s : Fin n → BananaSort}
    (pair : V .left → V .right → F2) (x : ∀ i, V (s i)) (y : Fin n → V .left ⊕ V .right)
    (h : letI := bananaTaggedPairingStructure pair
      SameFormulaType (L := bananaTaggedLanguage) (fun i => tag (x i)) y) (i : Fin n) :
    ∃ z : V (s i), y i = tag z := by
  let _ := bananaTaggedPairingStructure pair
  let rel : bananaTaggedLanguage.Relations 1 := match s i with
    | .left => .left
    | .right => .right
  let ψ := Language.Relations.formula₁ (L := bananaTaggedLanguage) rel (.var i)
  have realize (b : Fin n → V .left ⊕ V .right) :
      ψ.Realize b ↔ ∃ z : V (s i), b i = tag z := by
    dsimp only [ψ, rel]
    generalize s i = side
    cases side <;> exact Language.Formula.realize_rel₁ (L := bananaTaggedLanguage) (v := b)
  exact (realize y).mp ((h ψ).mp ((realize _).mpr ⟨x i, rfl⟩))

/-- In the tagged structure each target coordinate has the required sort.
The two translations identify the sorted source copies and preserve the
colour bits even when some coordinates are repeated. -/
theorem HasSortedDefinableTupleRamsey.of_tagged (pair : V .left → V .right → F2)
    (h : letI := bananaTaggedPairingStructure pair
      HasDefinableTupleRamsey bananaTaggedLanguage (V .left ⊕ V .right)) :
    HasSortedDefinableTupleRamsey pair := by
  classical
  let _ := bananaTaggedPairingStructure pair
  intro l r k c aSort bSort pSort a b p φ
  obtain ⟨d, hd, hmono⟩ := h (fun i => tag (a i)) (fun i => tag (b i))
    (fun i => tag (p i)) (fun t => translateWithZeros (φ t))
  choose d' htag using exists_tag_eq_of_sameFormulaType pair b d hd
  have hd' : (fun i => tag (d' i)) = d := funext fun i => (htag i).symm
  refine ⟨d', (sameFormulaType_iff_sorted pair b d').mp (by rwa [hd']), ?_⟩
  intro i j hi hj t
  have type (u : CompatibleIndices aSort bSort)
      (hu : SameSortedFormulaType pair a (restrictTuple u b)) :
      SameFormulaType (L := bananaTaggedLanguage) (fun j => tag (a j))
        ((fun j => tag (b j)) ∘ u.val) := by
    rw [← tag_restrictTuple]
    exact (sameFormulaType_iff_sorted pair a (restrictTuple u b)).mpr hu
  have color (u : CompatibleIndices aSort bSort) :
      (translateWithZeros (φ t)).Realize (Sum.elim (d ∘ u.val) (fun j => tag (p j))) ↔
        (φ t).realize pair (zeroExtend (sumTuple (restrictTuple u d') p)) := by
    have hcolor := realize_translateWithZeros pair (φ t) (sumTuple (restrictTuple u d') p)
    rw [tag_sumTuple, tag_restrictTuple, hd'] at hcolor
    exact hcolor
  exact (color i).symm.trans ((hmono i.val j.val (type i hi) (type j hj) t).trans (color j))

/-- The native two-sorted BANANA limit has definable tuple Ramsey. -/
theorem bananaLimit_hasSortedDefinableTupleRamsey :
    HasSortedDefinableTupleRamsey (V := fun _ => BananaLimitVector) bananaLimitPairing := by
  exact HasSortedDefinableTupleRamsey.of_tagged (V := fun _ => BananaLimitVector) bananaLimitPairing
    (@hasDefinableTupleRamsey_of_equiv bananaTaggedLanguage BananaTaggedCarrier BananaTaggedCarrier
      (bananaTaggedPairingStructure bananaLimitPairing) bananaTaggedStructure
      bananaTaggedNativePairingEquiv bananaLimit_hasDefinableTupleRamsey)

/-- The native sorted structure decoded from any model of the complete
tagged BANANA theory has definable tuple Ramsey. -/
theorem bananaTagged_completeTheory_hasSortedDefinableTupleRamsey
    (M : Type*) [bananaTaggedLanguage.Structure M]
    [M ⊨ bananaTaggedLanguage.completeTheory BananaTaggedCarrier] :
    HasSortedDefinableTupleRamsey (V := fun s => s.Carrier M)
      (fun x y => bananaTaggedModelPairing (M := M) x y) := by
  let _ := bananaTaggedPairingStructure (fun x y => bananaTaggedModelPairing (M := M) x y)
  intro l r k c
  exact HasSortedDefinableTupleRamsey.of_tagged (V := fun s => s.Carrier M)
    (fun x y => bananaTaggedModelPairing (M := M) x y)
    (hasDefinableTupleRamsey_of_equiv (bananaTaggedModelPairingEquiv (M := M))
      (bananaTagged_completeTheory_hasDefinableTupleRamsey M))

end BananaSorted

end SuccessorTree.NonPrecompact
