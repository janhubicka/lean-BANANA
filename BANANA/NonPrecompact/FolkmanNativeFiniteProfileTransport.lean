import BANANA.NonPrecompact.FolkmanGeneratedTwoSortProfileIso

/-!
# Native two-sort Folkman profiles through faithful finite presentations

A presentation supplies canonical ring operations in finite atom codes
and exact reconstruction of the original F₂-valued pairing. Equal
finite tuple profiles then give an isomorphism of the *original*
finitely generated non-unital two-sorted rings, including their
distinguished generators and their pairing.

This is deliberately parametric in finite presentations, so that it
does not depend on the unverified Fin-index work in draft PR #305.
It includes the zero ring in either sort and empty tuples. It does
not construct a homogeneous countable limit or infer oligomorphicity.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators symmDiff

/-- Faithful finite atom coordinates for a native Boolean ring.
There is no condition that embeddings preserve the ambient unit. -/
structure FolkmanFiniteRingPresentation
    (α : Type*) [BooleanRing α] (atoms : ℕ) where
  encode : α ≃ Finset (Fin atoms)
  map_zero : encode 0 = ∅
  map_add : ∀ x y, encode (x + y) =
    symmDiff (encode x) (encode y)
  map_mul : ∀ x y, encode (x * y) =
    encode x ∩ encode y

/-- Ring-term evaluation commutes with a faithful finite presentation. -/
theorem FolkmanFiniteRingPresentation.eval_term
    {α : Type*} [BooleanRing α] {atoms n : ℕ}
    (P : FolkmanFiniteRingPresentation α atoms)
    (xs : Fin n → α) (t : FolkmanRingTerm n) :
    P.encode (t.eval xs) =
      t.evalSet (fun i => P.encode (xs i)) := by
  classical
  let f : α → AsBoolRing (Finset (Fin atoms)) :=
    fun x => toBoolRing (P.encode x)
  have hzero : f 0 = 0 := by
    change toBoolRing (P.encode (0 : α)) = 0
    rw [P.map_zero]
    rfl
  have hadd : ∀ x y : α, f (x + y) = f x + f y := by
    intro x y
    change toBoolRing (P.encode (x + y)) =
      toBoolRing (P.encode x) + toBoolRing (P.encode y)
    rw [P.map_add, toBoolRing_symmDiff]
  have hmul : ∀ x y : α, f (x * y) = f x * f y := by
    intro x y
    change toBoolRing (P.encode (x * y)) =
      toBoolRing (P.encode x) * toBoolRing (P.encode y)
    rw [P.map_mul, toBoolRing_inf]
  have ht := FolkmanRingTerm.eval_map f hzero hadd hmul xs t
  have hc := t.eval_toBoolRing (fun i => P.encode (xs i))
  exact (toBoolRing.injective (ht.trans hc))

/-- A fully faithful presentation of a native two-sort finite pairing.
The pairing formula is required on every pair of native elements,
not just atoms or distinguished generators. -/
structure FolkmanFinitePairingPresentation
    (L R : Type*) [BooleanRing L] [BooleanRing R]
    (γ : L → R → F2) where
  atom : FolkmanAtomStructure
  leftCode : FolkmanFiniteRingPresentation L atom.leftCount
  rightCode : FolkmanFiniteRingPresentation R atom.rightCount
  pairing_code : ∀ x y, γ x y =
    ∑ i ∈ leftCode.encode x,
      ∑ j ∈ rightCode.encode y, atom.edge i j

/-- Package the exact finite-index data exported by the native
presentation interface (Track B), without importing a draft PR.
Only additive and multiplicative preservation are requested, not
preservation of units by embeddings. -/
def FolkmanFinitePairingPresentation.ofCoordinates
    {L R : Type*} [BooleanRing L] [BooleanRing R]
    (γ : L → R → F2)
    (A : FolkmanAtomStructure)
    (eL : L ≃ Finset (Fin A.leftCount))
    (eR : R ≃ Finset (Fin A.rightCount))
    (hpair : ∀ x : L, ∀ y : R,
      γ x y = ∑ i ∈ eL x, ∑ j ∈ eR y, A.edge i j)
    (haddL : ∀ x x' : L, eL (x + x') =
      symmDiff (eL x) (eL x'))
    (haddR : ∀ y y' : R, eR (y + y') =
      symmDiff (eR y) (eR y'))
    (hmulL : ∀ x x' : L, eL (x * x') = eL x ∩ eL x')
    (hmulR : ∀ y y' : R, eR (y * y') = eR y ∩ eR y')
    (hzeroL : eL (0 : L) = ∅)
    (hzeroR : eR (0 : R) = ∅) :
    FolkmanFinitePairingPresentation L R γ where
  atom := A
  leftCode := {
    encode := eL
    map_zero := hzeroL
    map_add := haddL
    map_mul := hmulL
  }
  rightCode := {
    encode := eR
    map_zero := hzeroR
    map_add := haddR
    map_mul := hmulR
  }
  pairing_code := hpair

/-- Complete finite profile of a native two-sort tuple, computed in
a chosen faithful finite presentation. -/
noncomputable def FolkmanFinitePairingPresentation.tupleProfile
    {L R : Type*} [BooleanRing L] [BooleanRing R]
    {γ : L → R → F2}
    (P : FolkmanFinitePairingPresentation L R γ)
    {nL nR : ℕ}
    (xs : Fin nL → L) (ys : Fin nR → R) :
    FolkmanAtomTupleProfile nL nR :=
  folkmanAtomTupleProfile P.atom
    (fun i => P.leftCode.encode (xs i))
    (fun j => P.rightCode.encode (ys j))

/-- Equal realised nonzero signatures on faithful finite presentations
give the same ring-term equations in the *original* native rings. -/
theorem folkmanNativeRingTerm_equalities_of_presentations
    {α β : Type*} [BooleanRing α] [BooleanRing β]
    {na nb n : ℕ}
    (P : FolkmanFiniteRingPresentation α na)
    (Q : FolkmanFiniteRingPresentation β nb)
    (xs : Fin n → α) (ys : Fin n → β)
    (h : folkmanTupleNonzeroPatterns
        (fun i => P.encode (xs i)) =
      folkmanTupleNonzeroPatterns
        (fun i => Q.encode (ys i)))
    (t u : FolkmanRingTerm n) :
    (t.eval xs = u.eval xs) ↔ (t.eval ys = u.eval ys) := by
  have heq := folkmanRingTerm_equalities_of_patterns_eq
    (fun i => P.encode (xs i))
    (fun i => Q.encode (ys i)) h t u
  constructor
  · intro hsource
    apply Q.encode.injective
    calc
      Q.encode (t.eval ys) =
          t.evalSet (fun i => Q.encode (ys i)) :=
        Q.eval_term ys t
      _ = u.evalSet (fun i => Q.encode (ys i)) := by
        apply heq.mp
        calc
          t.evalSet (fun i => P.encode (xs i)) =
              P.encode (t.eval xs) := (P.eval_term xs t).symm
          _ = P.encode (u.eval xs) := congrArg P.encode hsource
          _ = u.evalSet (fun i => P.encode (xs i)) := P.eval_term xs u
      _ = Q.encode (u.eval ys) := (Q.eval_term ys u).symm
  · intro htarget
    apply P.encode.injective
    calc
      P.encode (t.eval xs) =
          t.evalSet (fun i => P.encode (xs i)) :=
        P.eval_term xs t
      _ = u.evalSet (fun i => P.encode (xs i)) := by
        apply heq.mpr
        calc
          t.evalSet (fun i => Q.encode (ys i)) =
              Q.encode (t.eval ys) := (Q.eval_term ys t).symm
          _ = Q.encode (u.eval ys) := congrArg Q.encode htarget
          _ = u.evalSet (fun i => Q.encode (ys i)) := Q.eval_term ys u
      _ = P.encode (u.eval xs) := (P.eval_term xs u).symm

/-- Pairings of *all* non-unital terms are determined by equal complete
profiles, now on the original native carriers rather than their codes. -/
theorem folkmanNativeRingTerm_pairing_of_profile_eq
    {LA RA LB RB : Type*}
    [BooleanRing LA] [BooleanRing RA]
    [BooleanRing LB] [BooleanRing RB]
    {γA : LA → RA → F2} {γB : LB → RB → F2}
    (P : FolkmanFinitePairingPresentation LA RA γA)
    (Q : FolkmanFinitePairingPresentation LB RB γB)
    {nL nR : ℕ}
    (xsA : Fin nL → LA) (ysA : Fin nR → RA)
    (xsB : Fin nL → LB) (ysB : Fin nR → RB)
    (h : P.tupleProfile xsA ysA = Q.tupleProfile xsB ysB)
    (t : FolkmanRingTerm nL) (u : FolkmanRingTerm nR) :
    γA (t.eval xsA) (u.eval ysA) =
      γB (t.eval xsB) (u.eval ysB) := by
  classical
  have hp := folkmanNonunitalTerm_pairing_of_profile_eq
    (fun i => P.leftCode.encode (xsA i))
    (fun j => P.rightCode.encode (ysA j))
    (fun i => Q.leftCode.encode (xsB i))
    (fun j => Q.rightCode.encode (ysB j))
    h t.toNonunitalTerm u.toNonunitalTerm
  calc
    γA (t.eval xsA) (u.eval ysA) =
        (∑ a ∈ P.leftCode.encode (t.eval xsA),
          ∑ b ∈ P.rightCode.encode (u.eval ysA), P.atom.edge a b) :=
      P.pairing_code _ _
    _ = (∑ a ∈ t.evalSet (fun i => P.leftCode.encode (xsA i)),
          ∑ b ∈ u.evalSet (fun j => P.rightCode.encode (ysA j)),
            P.atom.edge a b) := by
        rw [P.leftCode.eval_term xsA t,
          P.rightCode.eval_term ysA u]
    _ = (∑ a ∈ t.toNonunitalTerm.val.evalSet
          (fun i => P.leftCode.encode (xsA i)),
          ∑ b ∈ u.toNonunitalTerm.val.evalSet
            (fun j => P.rightCode.encode (ysA j)), P.atom.edge a b) := by
        rw [t.toNonunitalTerm_evalSet, u.toNonunitalTerm_evalSet]
    _ = (∑ a ∈ t.toNonunitalTerm.val.evalSet
          (fun i => Q.leftCode.encode (xsB i)),
          ∑ b ∈ u.toNonunitalTerm.val.evalSet
            (fun j => Q.rightCode.encode (ysB j)), Q.atom.edge a b) := hp
    _ = (∑ a ∈ Q.leftCode.encode (t.eval xsB),
          ∑ b ∈ Q.rightCode.encode (u.eval ysB), Q.atom.edge a b) := by
        rw [t.toNonunitalTerm_evalSet, u.toNonunitalTerm_evalSet,
          ← Q.leftCode.eval_term xsB t, ← Q.rightCode.eval_term ysB u]
    _ = γB (t.eval xsB) (u.eval ysB) := (Q.pairing_code _ _).symm

/-- An element of a native generated non-unital ring named by a tuple
coordinate, without inserting an ambient multiplicative identity. -/
def folkmanNativeGeneratedCoordinate
    {α : Type*} [BooleanRing α] {n : ℕ}
    (xs : Fin n → α) (i : Fin n) :
    folkmanGeneratedNonunitalSubring xs :=
  ⟨xs i, (FolkmanRingTerm.generator i).eval_mem_generated xs⟩

/-- Finite original-language isomorphism of *generated* two-sort
non-unital Folkman structures, preserving the full pairing. -/
structure FolkmanNativeGeneratedTwoSortIso
    {LA RA LB RB : Type*}
    [BooleanRing LA] [BooleanRing RA]
    [BooleanRing LB] [BooleanRing RB]
    (γA : LA → RA → F2) (γB : LB → RB → F2)
    {nL nR : ℕ}
    (xsA : Fin nL → LA) (ysA : Fin nR → RA)
    (xsB : Fin nL → LB) (ysB : Fin nR → RB) where
  left : folkmanGeneratedNonunitalSubring xsA ≃+*
    folkmanGeneratedNonunitalSubring xsB
  right : folkmanGeneratedNonunitalSubring ysA ≃+*
    folkmanGeneratedNonunitalSubring ysB
  left_generators : ∀ i,
    left (folkmanNativeGeneratedCoordinate xsA i) =
      folkmanNativeGeneratedCoordinate xsB i
  right_generators : ∀ i,
    right (folkmanNativeGeneratedCoordinate ysA i) =
      folkmanNativeGeneratedCoordinate ysB i
  pairing : ∀ (x : folkmanGeneratedNonunitalSubring xsA)
      (y : folkmanGeneratedNonunitalSubring ysA),
    γB (left x).val (right y).val = γA x.val y.val

/-- Equal complete profiles under faithful finite presentations yield
an isomorphism of the original generated native two-sort structures.

The hypotheses state finite-presentation fidelity on all elements
and use no homogeneous-limit automorphism-extension assumption. -/
noncomputable def folkmanNativeGeneratedTwoSortIso_of_profile_eq
    {LA RA LB RB : Type*}
    [BooleanRing LA] [BooleanRing RA]
    [BooleanRing LB] [BooleanRing RB]
    {γA : LA → RA → F2} {γB : LB → RB → F2}
    (P : FolkmanFinitePairingPresentation LA RA γA)
    (Q : FolkmanFinitePairingPresentation LB RB γB)
    {nL nR : ℕ}
    (xsA : Fin nL → LA) (ysA : Fin nR → RA)
    (xsB : Fin nL → LB) (ysB : Fin nR → RB)
    (h : P.tupleProfile xsA ysA = Q.tupleProfile xsB ysB) :
    FolkmanNativeGeneratedTwoSortIso γA γB xsA ysA xsB ysB := by
  classical
  let hL : folkmanTupleNonzeroPatterns
      (fun i => P.leftCode.encode (xsA i)) =
      folkmanTupleNonzeroPatterns
        (fun i => Q.leftCode.encode (xsB i)) :=
    congrArg (fun z : FolkmanAtomTupleProfile nL nR => z.1.1) h
  let hR : folkmanTupleNonzeroPatterns
      (fun i => P.rightCode.encode (ysA i)) =
      folkmanTupleNonzeroPatterns
        (fun i => Q.rightCode.encode (ysB i)) :=
    congrArg (fun z : FolkmanAtomTupleProfile nL nR => z.1.2) h
  let heqL : ∀ t u : FolkmanRingTerm nL,
      t.eval xsA = u.eval xsA ↔ t.eval xsB = u.eval xsB :=
    folkmanNativeRingTerm_equalities_of_presentations
      P.leftCode Q.leftCode xsA xsB hL
  let heqR : ∀ t u : FolkmanRingTerm nR,
      t.eval ysA = u.eval ysA ↔ t.eval ysB = u.eval ysB :=
    folkmanNativeRingTerm_equalities_of_presentations
      P.rightCode Q.rightCode ysA ysB hR
  refine {
    left := folkmanGeneratedNonunitalRingEquiv_of_termEqualities xsA xsB heqL
    right := folkmanGeneratedNonunitalRingEquiv_of_termEqualities ysA ysB heqR
    left_generators := ?_
    right_generators := ?_
    pairing := ?_
  }
  · intro i
    apply Subtype.ext
    exact folkmanGeneratedNonunitalRingEquiv_generator xsA xsB heqL i
  · intro i
    apply Subtype.ext
    exact folkmanGeneratedNonunitalRingEquiv_generator ysA ysB heqR i
  · intro x y
    let t : FolkmanRingTerm nL :=
      folkmanGeneratedRingTermRepresentative xsA x
    let u : FolkmanRingTerm nR :=
      folkmanGeneratedRingTermRepresentative ysA y
    have ht : t.eval xsA = x.val :=
      folkmanGeneratedRingTermRepresentative_spec xsA x
    have hu : u.eval ysA = y.val :=
      folkmanGeneratedRingTermRepresentative_spec ysA y
    have htB : (folkmanGeneratedNonunitalRingEquiv_of_termEqualities
        xsA xsB heqL x).val = t.eval xsB :=
      folkmanGeneratedNonunitalRingEquiv_eval_term
        xsA xsB heqL x t ht
    have huB : (folkmanGeneratedNonunitalRingEquiv_of_termEqualities
        ysA ysB heqR y).val = u.eval ysB :=
      folkmanGeneratedNonunitalRingEquiv_eval_term
        ysA ysB heqR y u hu
    calc
      γB (folkmanGeneratedNonunitalRingEquiv_of_termEqualities
          xsA xsB heqL x).val
        (folkmanGeneratedNonunitalRingEquiv_of_termEqualities
          ysA ysB heqR y).val =
        γB (t.eval xsB) (u.eval ysB) := by rw [htB, huB]
      _ = γA (t.eval xsA) (u.eval ysA) :=
        (folkmanNativeRingTerm_pairing_of_profile_eq
          P Q xsA ysA xsB ysB h t u).symm
      _ = γA x.val y.val := by rw [ht, hu]

end SuccessorTree.NonPrecompact
