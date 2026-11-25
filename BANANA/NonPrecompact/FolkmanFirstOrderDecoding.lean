import BANANA.NonPrecompact.FolkmanFirstOrderLanguage
import BANANA.NonPrecompact.FolkmanNativePairing
import Mathlib.ModelTheory.Bundled
import Mathlib.RingTheory.NonUnitalSubring.Basic
import Mathlib.Tactic.FinCases

/-!
# Recovering the original ring sorts of a Folkman structure

When each finite tuple factors through a paired Boolean-ring product,
the ring and projection identities hold on the whole structure. The
coordinate ranges recover the two non-unital rings, and the pairing
relations recover their additive pairing.
-/

namespace SuccessorTree.NonPrecompact.FolkmanDecoding

open FirstOrder CategoryTheory
open scoped FirstOrder

/-- A native paired Boolean-ring product which can witness a finite tuple. -/
structure PairedProduct where
  Left : Type
  Right : Type
  [leftRing : BooleanRing Left]
  [rightRing : BooleanRing Right]
  data : FolkmanNativeFinitePairing Left Right

attribute [instance] PairedProduct.leftRing PairedProduct.rightRing

/-- The first-order encoding of a native paired product. -/
def PairedProduct.bundle (P : PairedProduct) : Bundled.{0} folkmanLanguage.Structure :=
  ⟨P.Left × P.Right, folkmanProductStructure P.data.pairing⟩

/-- The elements of each finite tuple lie in one embedded native paired product. -/
def FactorsThroughPairedProducts (M : Bundled.{0} folkmanLanguage.Structure) : Prop :=
  ∀ {n : ℕ} (xs : Fin n → M),
    ∃ (P : PairedProduct) (e : P.bundle ↪[folkmanLanguage] M)
      (ys : Fin n → P.bundle), ∀ i, e (ys i) = xs i

variable (M : Bundled.{0} folkmanLanguage.Structure)

private abbrev zero : M :=
  Language.Structure.funMap (L := folkmanLanguage) FolkmanFunction.zero Fin.elim0

private abbrev add (x y : M) : M :=
  Language.Structure.funMap (L := folkmanLanguage) FolkmanFunction.add ![x, y]

private abbrev mul (x y : M) : M :=
  Language.Structure.funMap (L := folkmanLanguage) FolkmanFunction.mul ![x, y]

/-- Apply the left sort projection of the first-order structure. -/
abbrev left (x : M) : M :=
  Language.Structure.funMap (L := folkmanLanguage) FolkmanFunction.left (fun _ => x)

/-- Apply the right sort projection of the first-order structure. -/
abbrev right (x : M) : M :=
  Language.Structure.funMap (L := folkmanLanguage) FolkmanFunction.right (fun _ => x)

variable {M}

private theorem map_zero {N : Bundled.{0} folkmanLanguage.Structure}
    (e : M ↪[folkmanLanguage] N) : zero N = e (zero M) := by
  have h := (e.map_fun (FolkmanFunction.zero : folkmanLanguage.Functions 0) Fin.elim0).symm
  rw [show (e ∘ (Fin.elim0 : Fin 0 → M)) = (Fin.elim0 : Fin 0 → N)
    from funext fun i => i.elim0] at h
  exact h

private theorem map_add {N : Bundled.{0} folkmanLanguage.Structure}
    (e : M ↪[folkmanLanguage] N) (x y : M) : add N (e x) (e y) = e (add M x y) := by
  have h : (e ∘ ![x, y]) = ![e x, e y] := by
    funext i
    fin_cases i <;> rfl
  have he := (e.map_fun (FolkmanFunction.add : folkmanLanguage.Functions 2) ![x, y]).symm
  rw [h] at he
  exact he

private theorem map_mul {N : Bundled.{0} folkmanLanguage.Structure}
    (e : M ↪[folkmanLanguage] N) (x y : M) : mul N (e x) (e y) = e (mul M x y) := by
  have h : (e ∘ ![x, y]) = ![e x, e y] := by
    funext i
    fin_cases i <;> rfl
  have he := (e.map_fun (FolkmanFunction.mul : folkmanLanguage.Functions 2) ![x, y]).symm
  rw [h] at he
  exact he

private theorem map_left {N : Bundled.{0} folkmanLanguage.Structure}
    (e : M ↪[folkmanLanguage] N) (x : M) : left N (e x) = e (left M x) :=
  (e.map_fun (FolkmanFunction.left : folkmanLanguage.Functions 1) (fun _ => x)).symm

private theorem map_right {N : Bundled.{0} folkmanLanguage.Structure}
    (e : M ↪[folkmanLanguage] N) (x : M) : right N (e x) = e (right M x) :=
  (e.map_fun (FolkmanFunction.right : folkmanLanguage.Functions 1) (fun _ => x)).symm

private structure LawsAt (M : Bundled.{0} folkmanLanguage.Structure) (x y z : M) : Prop where
  add_assoc : add M (add M x y) z = add M x (add M y z)
  add_comm : add M x y = add M y x
  add_zero : add M x (zero M) = x
  zero_add : add M (zero M) x = x
  add_self : add M x x = zero M
  mul_assoc : mul M (mul M x y) z = mul M x (mul M y z)
  mul_comm : mul M x y = mul M y x
  mul_zero : mul M x (zero M) = zero M
  zero_mul : mul M (zero M) x = zero M
  mul_self : mul M x x = x
  mul_add : mul M x (add M y z) = add M (mul M x y) (mul M x z)
  add_mul : mul M (add M x y) z = add M (mul M x z) (mul M y z)
  left_zero : left M (zero M) = zero M
  left_add : left M (add M x y) = add M (left M x) (left M y)
  left_mul : left M (mul M x y) = mul M (left M x) (left M y)
  right_zero : right M (zero M) = zero M
  right_add : right M (add M x y) = add M (right M x) (right M y)
  right_mul : right M (mul M x y) = mul M (right M x) (right M y)
  left_left : left M (left M x) = left M x
  right_right : right M (right M x) = right M x
  left_right : left M (right M x) = zero M
  right_left : right M (left M x) = zero M
  decompose : add M (left M x) (right M x) = x

private theorem native_laws (P : PairedProduct) (x y z : P.bundle) :
    LawsAt P.bundle x y z := by
  change P.Left × P.Right at x y z
  refine ⟨add_assoc x y z, add_comm x y, add_zero x, zero_add x, ?_, mul_assoc x y z,
    mul_comm x y, mul_zero x, zero_mul x, ?_, mul_add x y z, add_mul x y z, rfl, ?_, ?_, rfl, ?_, ?_,
    rfl, rfl, rfl, rfl, ?_⟩
  · exact Prod.ext (BooleanRing.add_self x.1) (BooleanRing.add_self x.2)
  · exact Prod.ext (BooleanRing.mul_self x.1) (BooleanRing.mul_self x.2)
  · exact Prod.ext rfl (zero_add (0 : P.Right)).symm
  · exact Prod.ext rfl (zero_mul (0 : P.Right)).symm
  · exact Prod.ext (zero_add (0 : P.Left)).symm rfl
  · exact Prod.ext (zero_mul (0 : P.Left)).symm rfl
  · exact Prod.ext (add_zero x.1) (zero_add x.2)

variable (M) (hM : FactorsThroughPairedProducts M)

include hM in
private theorem laws (x y z : M) : LawsAt M x y z := by
  obtain ⟨P, e, xyz, he⟩ := hM ![x, y, z]
  have hx : e (xyz 0) = x := he 0
  have hy : e (xyz 1) = y := he 1
  have hz : e (xyz 2) = z := he 2
  subst x
  subst y
  subst z
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    native_laws P (xyz 0) (xyz 1) (xyz 2)
  constructor <;> simp only [map_zero e, map_add e, map_mul e, map_left e, map_right e] <;>
    apply congrArg e <;> assumption

/-- The decoded product carries its original non-unital Boolean ring
operations. In characteristic two additive negation is the identity. -/
@[instance_reducible]
def productRing : NonUnitalCommRing M where
  zero := zero M
  add := add M
  mul := mul M
  neg := id
  add_assoc x y z := (laws M hM x y z).add_assoc
  add_comm x y := (laws M hM x y y).add_comm
  zero_add x := (laws M hM x x x).zero_add
  add_zero x := (laws M hM x x x).add_zero
  neg_add_cancel x := (laws M hM x x x).add_self
  mul_assoc x y z := (laws M hM x y z).mul_assoc
  mul_comm x y := (laws M hM x y y).mul_comm
  zero_mul x := (laws M hM x x x).zero_mul
  mul_zero x := (laws M hM x x x).mul_zero
  left_distrib x y z := (laws M hM x y z).mul_add
  right_distrib x y z := (laws M hM x y z).add_mul
  nsmul := letI : Zero M := ⟨zero M⟩; letI : Add M := ⟨add M⟩; nsmulRec
  zsmul := letI : Zero M := ⟨zero M⟩; letI : Add M := ⟨add M⟩; letI : Neg M := ⟨id⟩; zsmulRec

theorem productRing_mul_self (x : M) :
    letI := productRing M hM
    x * x = x :=
  (laws M hM x x x).mul_self

/-- Left axis of the encoded product, as a non-unital ring projection. -/
def leftProjection : letI := productRing M hM; M →ₙ+* M := by
  letI := productRing M hM
  exact {
    toFun := left M
    map_zero' := (laws M hM (zero M) (zero M) (zero M)).left_zero
    map_add' := fun x y => (laws M hM x y y).left_add
    map_mul' := fun x y => (laws M hM x y y).left_mul }

/-- Right axis of the encoded product, as a non-unital ring projection. -/
def rightProjection : letI := productRing M hM; M →ₙ+* M := by
  letI := productRing M hM
  exact {
    toFun := right M
    map_zero' := (laws M hM (zero M) (zero M) (zero M)).right_zero
    map_add' := fun x y => (laws M hM x y y).right_add
    map_mul' := fun x y => (laws M hM x y y).right_mul }

/-- A decoded coordinate is an element of the projection range. -/
def leftSort : letI := productRing M hM; NonUnitalSubring M := by
  letI := productRing M hM
  exact (leftProjection M hM).range

/-- A decoded coordinate is an element of the projection range. -/
def rightSort : letI := productRing M hM; NonUnitalSubring M := by
  letI := productRing M hM
  exact (rightProjection M hM).range

/-- The carrier splits into the product of its original ring sorts,
by addition of the left and right coordinates. -/
def productEquiv :
    letI := productRing M hM
    (leftSort M hM × rightSort M hM) ≃ M := by
  letI := productRing M hM
  refine {
    toFun := fun pq => (pq.1 : M) + (pq.2 : M)
    invFun := fun x => (⟨left M x, ⟨x, rfl⟩⟩, ⟨right M x, ⟨x, rfl⟩⟩)
    left_inv := ?_
    right_inv := fun x => (laws M hM x x x).decompose }
  rintro ⟨⟨_, ⟨x, rfl⟩⟩, ⟨_, ⟨y, rfl⟩⟩⟩
  apply Prod.ext <;> apply Subtype.ext
  · change left M (add M (left M x) (right M y)) = left M x
    rw [(laws M hM (left M x) (right M y) y).left_add,
      (laws M hM x x x).left_left, (laws M hM y y y).left_right,
      (laws M hM (left M x) x x).add_zero]
  · change right M (add M (left M x) (right M y)) = right M y
    rw [(laws M hM (left M x) (right M y) y).right_add,
      (laws M hM x x x).right_left, (laws M hM y y y).right_right,
      (laws M hM (right M y) y y).zero_add]

private abbrev pairRel (M : Bundled.{0} folkmanLanguage.Structure)
    (a : ZMod 2) (x y : M) : Prop :=
  Language.Structure.RelMap (L := folkmanLanguage) (FolkmanRelation.pair a) ![x, y]

private theorem pairRel_map
    {N P : Bundled.{0} folkmanLanguage.Structure} (e : N ↪[folkmanLanguage] P)
    (a : ZMod 2) (x y : N) :
    pairRel P a (e x) (e y) ↔ pairRel N a x y := by
  have h : (e ∘ ![x, y]) = ![e x, e y] := by
    funext i
    fin_cases i <;> rfl
  have he := e.map_rel (FolkmanRelation.pair a : folkmanLanguage.Relations 2) ![x, y]
  rw [h] at he
  exact he

include hM in
private theorem pair_existsUnique (x y : M) : ∃! a : ZMod 2, pairRel M a x y := by
  obtain ⟨P, e, xy, he⟩ := hM ![x, y]
  have hx : e (xy 0) = x := he 0
  have hy : e (xy 1) = y := he 1
  rw [← hx, ← hy]
  let a := P.data.pairing (xy 0).1 (xy 1).2
  exact ⟨a, (pairRel_map e a _ _).2 rfl,
    fun b hb => ((pairRel_map e b _ _).1 hb : a = b).symm⟩

private noncomputable def pair (x y : M) : ZMod 2 :=
  Classical.choose (pair_existsUnique M hM x y)

private theorem pair_eq_iff (x y : M) (a : ZMod 2) : pair M hM x y = a ↔ pairRel M a x y := by
  have h := Classical.choose_spec (pair_existsUnique M hM x y)
  exact ⟨fun ha => ha ▸ h.1, fun ha => (h.2 a ha).symm⟩

private theorem pair_map {P : PairedProduct}
    (e : P.bundle ↪[folkmanLanguage] M)
    (x y : P.bundle) :
    pair M hM (e x) (e y) = P.data.pairing x.1 y.2 :=
  (pair_eq_iff M hM _ _ _).2 ((pairRel_map e _ x y).2 rfl)

private theorem pair_add_left (x y z : M) :
    pair M hM (add M x y) z = pair M hM x z + pair M hM y z := by
  obtain ⟨P, e, xyz, he⟩ := hM ![x, y, z]
  have hx : e (xyz 0) = x := he 0
  have hy : e (xyz 1) = y := he 1
  have hz : e (xyz 2) = z := he 2
  rw [← hx, ← hy, ← hz, map_add, pair_map, pair_map, pair_map]
  exact P.data.add_left _ _ _

private theorem pair_add_right (x y z : M) :
    pair M hM x (add M y z) = pair M hM x y + pair M hM x z := by
  obtain ⟨P, e, xyz, he⟩ := hM ![x, y, z]
  have hx : e (xyz 0) = x := he 0
  have hy : e (xyz 1) = y := he 1
  have hz : e (xyz 2) = z := he 2
  rw [← hx, ← hy, ← hz, map_add, pair_map, pair_map, pair_map]
  exact P.data.add_right _ _ _

private theorem pair_projects (x y : M) :
    pair M hM (left M x) (right M y) = pair M hM x y := by
  obtain ⟨P, e, xy, he⟩ := hM ![x, y]
  have hx : e (xy 0) = x := he 0
  have hy : e (xy 1) = y := he 1
  rw [← hx, ← hy, map_left, map_right, pair_map, pair_map]
  rfl

/-- The recovered binary pairing of the decoded left and right rings. -/
noncomputable def pairing :
    letI := productRing M hM
    leftSort M hM → rightSort M hM → ZMod 2 :=
  fun a b => pair M hM a b

theorem pairing_add_left :
    letI := productRing M hM
    ∀ (a a' : leftSort M hM) (b : rightSort M hM),
      pairing M hM (a + a') b = pairing M hM a b + pairing M hM a' b := by
  intro a a' b
  exact pair_add_left M hM a a' b

theorem pairing_add_right :
    letI := productRing M hM
    ∀ (a : leftSort M hM) (b b' : rightSort M hM),
      pairing M hM a (b + b') = pairing M hM a b + pairing M hM a b' := by
  intro a b b'
  exact pair_add_right M hM a b b'

/-- Re-encoding the recovered native sorts and pairing gives back the
first-order structure, including the two sort projections. -/
noncomputable def encodingEquiv :
    letI := productRing M hM
    letI := folkmanProductStructure (pairing M hM)
    M ≃[folkmanLanguage] (leftSort M hM × rightSort M hM) := by
  letI := productRing M hM
  letI := folkmanProductStructure (pairing M hM)
  refine {
    toEquiv := (productEquiv M hM).symm
    map_fun' := ?_
    map_rel' := ?_ }
  · intro n op xs
    cases op with
    | zero =>
      rw [show xs = Fin.elim0 from funext fun i => i.elim0]
      have h := laws M hM (zero M) (zero M) (zero M)
      exact Prod.ext (Subtype.ext h.left_zero) (Subtype.ext h.right_zero)
    | add =>
      rw [show xs = ![xs 0, xs 1] from funext fun i => by fin_cases i <;> rfl]
      have h := laws M hM (xs 0) (xs 1) (xs 1)
      exact Prod.ext (Subtype.ext h.left_add) (Subtype.ext h.right_add)
    | mul =>
      rw [show xs = ![xs 0, xs 1] from funext fun i => by fin_cases i <;> rfl]
      have h := laws M hM (xs 0) (xs 1) (xs 1)
      exact Prod.ext (Subtype.ext h.left_mul) (Subtype.ext h.right_mul)
    | left =>
      rw [show xs = (fun _ => xs 0) from funext fun i => by fin_cases i; rfl]
      have h := laws M hM (xs 0) (xs 0) (xs 0)
      exact Prod.ext (Subtype.ext h.left_left) (Subtype.ext h.right_left)
    | right =>
      rw [show xs = (fun _ => xs 0) from funext fun i => by fin_cases i; rfl]
      have h := laws M hM (xs 0) (xs 0) (xs 0)
      exact Prod.ext (Subtype.ext h.left_right) (Subtype.ext h.right_right)
  · intro n rel xs
    cases rel with
    | pair a =>
      change pair M hM (left M (xs 0)) (right M (xs 1)) = a ↔ _
      rw [pair_projects]
      have h : ![xs 0, xs 1] = xs := by
        funext i
        fin_cases i <;> rfl
      exact h ▸ (pair_eq_iff M hM (xs 0) (xs 1) a)

/-- The restriction of an encoded automorphism to the decoded left sort. -/
def leftSortRingEquivOf (e : M ≃[folkmanLanguage] M) :
    letI := productRing M hM
    leftSort M hM ≃+* leftSort M hM := by
  letI := productRing M hM
  let lift (e : M ≃[folkmanLanguage] M) (x : leftSort M hM) : leftSort M hM :=
    ⟨e x.val, by
      rcases x.property with ⟨y, hy⟩
      exact ⟨e y, (map_left e.toEmbedding y).trans (congrArg e hy)⟩⟩
  refine {
    toFun := lift e
    invFun := lift e.symm
    left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
    right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val)
    map_add' := fun x y => Subtype.ext (map_add e.toEmbedding x.val y.val).symm
    map_mul' := fun x y => Subtype.ext (map_mul e.toEmbedding x.val y.val).symm }

theorem leftSortRingEquivOf_apply (e : M ≃[folkmanLanguage] M) (x : leftSort M hM) :
    ((leftSortRingEquivOf M hM e x : leftSort M hM) : M) = e x.val := rfl

end SuccessorTree.NonPrecompact.FolkmanDecoding
