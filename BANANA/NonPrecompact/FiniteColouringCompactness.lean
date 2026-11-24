import Mathlib.Topology.Compactness.Compact

/-!
# From global colourings to a finite support

An acceptable witness is a condition on finitely many coordinates. If
every global colouring has such a witness, the same is true on a single
finite set containing the supports of finitely many witnesses.
-/

namespace SuccessorTree.NonPrecompact

open Set

/-- Compactness of the space of colourings gives a common finite support for
an acceptable witness. Local finiteness of a structure can then put that
support inside a finite ambient structure. -/
theorem exists_finite_support_of_colourings
    {X T Colour : Type*} [TopologicalSpace Colour] [CompactSpace Colour]
    [DiscreteTopology Colour] [Nonempty Colour]
    (support : T → Finset X)
    (good : ∀ t : T, ((support t) → Colour) → Prop)
    (hglobal : ∀ c : X → Colour, ∃ t, good t ((support t).restrict c)) :
    ∃ s : Finset X, ∀ c : s → Colour,
      ∃ (t : T) (h : support t ⊆ s), good t (fun x => c ⟨x, h x.property⟩) := by
  classical
  let U (t : T) : Set (X → Colour) :=
    (support t).restrict ⁻¹' {c | good t c}
  have hopen (t) : IsOpen (U t) :=
    (isOpen_discrete _).preimage ((support t).continuous_restrict)
  have hcover : (univ : Set (X → Colour)) ⊆ ⋃ t, U t := fun c _ => by
    obtain ⟨t, ht⟩ := hglobal c
    exact mem_iUnion.2 ⟨t, ht⟩
  obtain ⟨ts, hts⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  let s := ts.biUnion support
  refine ⟨s, ?_⟩
  intro c
  let padded : X → Colour := fun x =>
    if hx : x ∈ s then c ⟨x, hx⟩ else Classical.choice ‹Nonempty Colour›
  obtain ⟨t, ht⟩ := mem_iUnion.1 (hts (mem_univ padded))
  obtain ⟨hts', hgood⟩ := mem_iUnion.1 ht
  have hs : support t ⊆ s := fun x hx =>
    Finset.mem_biUnion.2 ⟨t, hts', hx⟩
  refine ⟨t, hs, ?_⟩
  change good t ((support t).restrict padded) at hgood
  have hrestrict : (support t).restrict padded =
      fun (x : support t) => c ⟨x, hs x.property⟩ := by
    funext x
    change (if hx : (x : X) ∈ s then c ⟨x, hx⟩ else Classical.choice ‹Nonempty Colour›)
      = c ⟨x, hs x.property⟩
    simp [hs x.property]
  rwa [← hrestrict]

end SuccessorTree.NonPrecompact
