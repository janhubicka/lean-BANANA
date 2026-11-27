import BANANA.CopyRamsey
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Copy Ramsey degrees bounded by expansion isomorphism types

For genuine range copies, precomposing an embedding by an automorphism
leaves its range unchanged. This allows the Ramsey argument to normalise
each induced expansion to a chosen isomorphism representative.
-/

namespace SuccessorTree

namespace FiniteCopySystem

/-- An invertible self-embedding of a reduct. -/
structure ReductAutomorphism (S : FiniteCopySystem) (A : S.Obj) where
  hom : S.Emb A A
  inv : S.Emb A A
  hom_inv : S.compEmb hom inv = S.idEmb A
  inv_hom : S.compEmb inv hom = S.idEmb A

namespace ReductAutomorphism

variable {S : FiniteCopySystem} {A : S.Obj}

/-- The identity automorphism of a reduct. -/
def refl (A : S.Obj) : S.ReductAutomorphism A :=
  ⟨S.idEmb A, S.idEmb A, S.comp_id_left _, S.comp_id_left _⟩

/-- The inverse of a reduct automorphism. -/
def symm (u : S.ReductAutomorphism A) : S.ReductAutomorphism A :=
  ⟨u.inv, u.hom, u.inv_hom, u.hom_inv⟩

/-- Compose the two reduct automorphisms, in embedding composition order. -/
def trans (u v : S.ReductAutomorphism A) : S.ReductAutomorphism A where
  hom := S.compEmb u.hom v.hom
  inv := S.compEmb v.inv u.inv
  hom_inv := by
    rw [S.comp_assoc, ← S.comp_assoc v.hom v.inv u.inv, v.hom_inv,
      S.comp_id_left, u.hom_inv]
  inv_hom := by
    rw [S.comp_assoc, ← S.comp_assoc u.inv u.hom v.hom, u.inv_hom,
      S.comp_id_left, v.inv_hom]

end ReductAutomorphism

end FiniteCopySystem

namespace RamseyExpansion

variable {S : FiniteCopySystem} (E : RamseyExpansion S)

attribute [local instance] FiniteCopySystem.copyFintype
attribute [local instance] FiniteCopySystem.copyDecidableEq

/-- Two labelled expansions of the same object are isomorphic if a
reduct automorphism restricts the second to the first. -/
def ExpansionIsomorphic {A : S.Obj} (a b : E.Exp A) : Prop :=
  ∃ u : S.ReductAutomorphism A, E.restrict u.hom b = a

/-- A representative of each expansion isomorphism type suffices. The
range law holds for copies given by unlabelled embedding images. -/
theorem copyRamseyDegreeLE_card_expansionRepresentatives
    (A : S.Obj) [DecidableEq (E.Exp A)] (representatives : Finset (E.Exp A))
    (hrange : ∀ {B : S.Obj} (e : S.Emb A B) (u : S.ReductAutomorphism A),
      S.range (S.compEmb u.hom e) = S.range e)
    (hcover : ∀ a : E.Exp A, ∃ t ∈ representatives, E.ExpansionIsomorphic t a) :
    S.CopyRamseyDegreeLE A representatives.card := by
  classical
  intro B r hr
  let b : E.Exp B := Classical.choice (E.expNonempty B)
  obtain ⟨C, c, hsim⟩ := E.simultaneous_ramsey representatives b r hr
  refine ⟨C, fun colouring => ?_⟩
  let expandedColour : ∀ a : E.Exp A, E.ExpEmb a c → Fin r :=
    fun _ e => colouring (S.range e.1)
  obtain ⟨g, hg⟩ := hsim expandedColour
  let rep : S.Copy A B → S.Emb A B :=
    fun p => Classical.choose (S.range_surjective p)
  have hrep (p : S.Copy A B) : S.range (rep p) = p :=
    Classical.choose_spec (S.range_surjective p)
  have htypes (p : S.Copy A B) :
      ∃ t ∈ representatives, ∃ u : S.ReductAutomorphism A,
        E.restrict u.hom (E.restrict (rep p) b) = t :=
    hcover (E.restrict (rep p) b)
  choose copyType htype u hu using htypes
  let normal (p : S.Copy A B) := S.compEmb (u p).hom (rep p)
  have hnormal (p : S.Copy A B) : E.restrict (normal p) b = copyType p := by
    change E.restrict (S.compEmb (u p).hom (rep p)) b = copyType p
    rw [E.restrict_comp, hu p]
  have hnormalRange (p : S.Copy A B) : S.range (normal p) = p :=
    (hrange (rep p) (u p)).trans (hrep p)
  let colourOn (p : S.Copy A B) := colouring (S.mapCopy g.1 p)
  have hsame (p q : S.Copy A B) (ht : copyType p = copyType q) :
      colourOn p = colourOn q := by
    let ep : E.ExpEmb (copyType p) b := ⟨normal p, hnormal p⟩
    let eq' : E.ExpEmb (copyType p) b := ⟨normal q, (hnormal q).trans ht.symm⟩
    have h := hg (copyType p) (htype p) ep eq'
    simpa only [colourOn, expandedColour, ep, eq', E.compExp_val, S.range_comp, hnormalRange] using h
  let colourByType (t : E.Exp A) :=
    if h : ∃ p, copyType p = t then colourOn (Classical.choose h) else ⟨0, hr⟩
  have hcolour (p : S.Copy A B) : colourOn p = colourByType (copyType p) := by
    have h : ∃ q, copyType q = copyType p := ⟨p, rfl⟩
    rw [show colourByType (copyType p) = colourOn (Classical.choose h) by
      simp only [colourByType, dite_eq_left h]]
    exact hsame p (Classical.choose h) (Classical.choose_spec h).symm
  refine ⟨g.1, ?_⟩
  have hsubset : S.coloursInside colouring g.1 ⊆ representatives.image colourByType := by
    intro v hv
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨copyType p, htype p, (hcolour p).symm⟩
  exact (Finset.card_le_card hsubset).trans Finset.card_image_le

/-- The actual quotient of labelled expansions by reduct automorphisms. -/
def expansionIsomorphismSetoid (A : S.Obj) : Setoid (E.Exp A) where
  r := E.ExpansionIsomorphic
  iseqv := {
    refl := fun a => ⟨FiniteCopySystem.ReductAutomorphism.refl A, E.restrict_id a⟩
    symm := by
      rintro a b ⟨u, hu⟩
      refine ⟨u.symm, ?_⟩
      change E.restrict u.inv a = b
      rw [← hu, ← E.restrict_comp, u.inv_hom, E.restrict_id]
    trans := by
      rintro a b c ⟨u, hu⟩ ⟨v, hv⟩
      refine ⟨u.trans v, ?_⟩
      change E.restrict (S.compEmb u.hom v.hom) c = a
      rw [E.restrict_comp, hv, hu] }

/-- The expansion bound counts isomorphism types, even when
several distinct labelled expansions give the same type. -/
theorem copyRamseyDegreeLE_card_expansionIsomorphismTypes (A : S.Obj)
    (hrange : ∀ {B : S.Obj} (e : S.Emb A B) (u : S.ReductAutomorphism A),
      S.range (S.compEmb u.hom e) = S.range e) :
    S.CopyRamseyDegreeLE A (Nat.card (Quotient (E.expansionIsomorphismSetoid A))) := by
  classical
  letI := E.expFintype A
  let Q := Quotient (E.expansionIsomorphismSetoid A)
  letI : Fintype Q := Fintype.ofFinite Q
  let representative : Q → E.Exp A := Quotient.out
  have hrep : Function.Injective representative := by
    intro a b hab
    exact (Quotient.out_eq a).symm.trans
      ((congrArg (Quotient.mk (E.expansionIsomorphismSetoid A)) hab).trans (Quotient.out_eq b))
  let representatives := Finset.univ.image representative
  have hcard : representatives.card = Nat.card Q := by
    rw [Finset.card_image_of_injective _ hrep, Finset.card_univ, Nat.card_eq_fintype_card]
  change S.CopyRamseyDegreeLE A (Nat.card Q)
  rw [← hcard]
  apply E.copyRamseyDegreeLE_card_expansionRepresentatives A representatives hrange
  intro a
  let q : Q := Quotient.mk (E.expansionIsomorphismSetoid A) a
  refine ⟨representative q, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩
  exact Quotient.exact (Quotient.out_eq q)

end RamseyExpansion

end SuccessorTree
