import BANANA.NonPrecompact.FolkmanFirstOrderSignature
import BANANA.NonPrecompact.FolkmanNativeFinitePairingClass

/-!
# The original two-sort Folkman pairing as a one-sorted first-order structure

A two-sorted non-unital Folkman pairing is represented on the disjoint
sum of its two carriers, with two named zeros, four binary ring
operations, two unary sort tags, and a binary relation for pairing one.

Each binary operation is totalised on wrong-sort inputs by returning
zero of its own output sort. In particular, the function symbols
cannot create new elements of the wrong sort. No multiplicative
identity is named, including when the ambient rings happen to have
one. Thus generated first-order substructures correspond to pairs
of generated non-unital subrings.

This module builds the interpretation only. Faithfulness of its
embeddings and transfer of native HP/JEP/AP remain separate
implementation and exact-head kernel-verification obligations.
-/

namespace SuccessorTree.NonPrecompact

/-- Left addition, with the original left zero as fallback if either
argument belongs to the right sort. -/
def folkmanTaggedAddLeft
    {L R : Type*} [NonUnitalRing L]
    (x y : Sum L R) : Sum L R :=
  match x, y with
  | .inl a, .inl b => .inl (a + b)
  | _, _ => .inl 0

/-- Left multiplication; the ambient unit is never used. -/
def folkmanTaggedMulLeft
    {L R : Type*} [NonUnitalRing L]
    (x y : Sum L R) : Sum L R :=
  match x, y with
  | .inl a, .inl b => .inl (a * b)
  | _, _ => .inl 0

/-- Right addition, with right zero on wrong-sort arguments. -/
def folkmanTaggedAddRight
    {L R : Type*} [NonUnitalRing R]
    (x y : Sum L R) : Sum L R :=
  match x, y with
  | .inr a, .inr b => .inr (a + b)
  | _, _ => .inr 0

/-- Right multiplication, without adjoining any ambient unit. -/
def folkmanTaggedMulRight
    {L R : Type*} [NonUnitalRing R]
    (x y : Sum L R) : Sum L R :=
  match x, y with
  | .inr a, .inr b => .inr (a * b)
  | _, _ => .inr 0

/-- The predicate tagging the left carrier. -/
def folkmanTaggedIsLeft {L R : Type*} : Sum L R → Prop
  | .inl _ => True
  | .inr _ => False

/-- The predicate tagging the right carrier. -/
def folkmanTaggedIsRight {L R : Type*} : Sum L R → Prop
  | .inl _ => False
  | .inr _ => True

/-- The original F₂-valued cross-sort pairing represented by the
binary relation recording value one; false off left × right. -/
def folkmanTaggedPairingOne
    {L R : Type*} (β : L → R → F2) :
    Sum L R → Sum L R → Prop
  | .inl x, .inr y => β x y = 1
  | _, _ => False

/-- The complete one-sorted first-order structure associated with
the original two-sorted non-unital ring pairing.

Symbol indices:
- constants 0,1 are left zero and right zero;
- binary functions 0,1,2,3 are left add, left mul, right add, right mul;
- unary relations 0,1 are left sort and right sort;
- the unique binary relation records pairing equal to one.

There are no named multiplicative units. -/
def folkmanTaggedFirstOrderStructure
    (L R : Type*) [NonUnitalRing L] [NonUnitalRing R]
    (β : L → R → F2) :
    folkmanFirstOrderLanguage.Structure (Sum L R) where
  funMap := by
    intro n f args
    by_cases hn0 : n = 0
    · subst n
      change Fin 2 at f
      exact if f = 0 then Sum.inl (0 : L) else Sum.inr (0 : R)
    · by_cases hn2 : n = 2
      · subst n
        change Fin 4 at f
        exact
          if f = 0 then
            folkmanTaggedAddLeft (args 0) (args 1)
          else if f = 1 then
            folkmanTaggedMulLeft (args 0) (args 1)
          else if f = 2 then
            folkmanTaggedAddRight (args 0) (args 1)
          else
            folkmanTaggedMulRight (args 0) (args 1)
      · have he : IsEmpty (folkmanFirstOrderLanguage.Functions n) := by
          change IsEmpty (folkmanFirstOrderFunctions n)
          simp [folkmanFirstOrderFunctions, hn0, hn2]
        exact isEmptyElim f
  RelMap := by
    intro n r args
    by_cases hn1 : n = 1
    · subst n
      change Fin 2 at r
      exact if r = 0 then folkmanTaggedIsLeft (args 0)
        else folkmanTaggedIsRight (args 0)
    · by_cases hn2 : n = 2
      · subst n
        change PUnit at r
        exact folkmanTaggedPairingOne β (args 0) (args 1)
      · have he : IsEmpty (folkmanFirstOrderLanguage.Relations n) := by
          change IsEmpty (folkmanFirstOrderRelations n)
          simp [folkmanFirstOrderRelations, hn1, hn2]
        exact isEmptyElim r

/-- The zeros are distinct tagged elements, even when both sorts
are the one-element zero ring. -/
theorem folkmanTaggedZeros_ne
    {L R : Type*} [Zero L] [Zero R] :
    (Sum.inl (0 : L) : Sum L R) ≠ Sum.inr (0 : R) := by
  intro h
  cases h

/-- Left addition on correctly tagged arguments is original addition. -/
theorem folkmanTaggedAddLeft_inl
    {L R : Type*} [NonUnitalRing L]
    (x y : L) :
    folkmanTaggedAddLeft (Sum.inl x : Sum L R) (.inl y) =
      .inl (x + y) := rfl

/-- Right multiplication is original multiplication on right inputs. -/
theorem folkmanTaggedMulRight_inr
    {L R : Type*} [NonUnitalRing R]
    (x y : R) :
    folkmanTaggedMulRight (Sum.inr x : Sum L R) (.inr y) =
      .inr (x * y) := rfl

/-- The pairing-one predicate on correctly tagged elements
recovers the original F₂-value-one predicate. -/
theorem folkmanTaggedPairingOne_inl_inr
    {L R : Type*} (β : L → R → F2)
    (x : L) (y : R) :
    folkmanTaggedPairingOne β (.inl x) (.inr y) ↔ β x y = 1 :=
  Iff.rfl

end SuccessorTree.NonPrecompact
