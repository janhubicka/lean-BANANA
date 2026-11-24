import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Topology.Separation.Profinite

/-!
# The Stone space of a Boolean algebra

The prime spectrum of the associated Boolean ring is compact Hausdorff. Its
basic opens are clopen, and they represent all the clopens. Boolean algebra
maps act on spectra by precomposition.
-/

namespace SuccessorTree.NonPrecompact.BooleanSpectrum

open TopologicalSpace

/-- The Stone space of a Boolean algebra, with the prime-spectrum topology. -/
abbrev Space (B : Type*) [BooleanAlgebra B] := PrimeSpectrum (AsBoolRing B)

variable {B C : Type*} [BooleanAlgebra B] [BooleanAlgebra C]

/-- Each Boolean element represents a basic clopen of the associated prime spectrum. -/
noncomputable def clopens : B ≃o Clopens (Space B) :=
  (show B ≃o {e : AsBoolRing B // IsIdempotentElem e} from
    { toFun := fun b => ⟨toBoolRing b, BooleanRing.isIdempotentElem _⟩
      invFun := fun e => ofBoolRing e.1
      left_inv := fun _ => rfl
      right_inv := fun _ => Subtype.ext rfl
      map_rel_iff' := ofBoolRing_le_ofBoolRing_iff.symm }).trans
    PrimeSpectrum.isIdempotentElemEquivClopens

@[simp] theorem coe_clopens (b : B) :
    (clopens b : Set (Space B)) = PrimeSpectrum.basicOpen (toBoolRing b) := rfl

/-- The Boolean representation as ordinary sets, for use with measures. -/
noncomputable def toSets : BoundedLatticeHom B (Set (Space B)) where
  toFun b := clopens b
  map_sup' a b := congrArg (fun c : Clopens (Space B) => (c : Set (Space B)))
    (map_sup clopens a b)
  map_inf' a b := congrArg (fun c : Clopens (Space B) => (c : Set (Space B)))
    (map_inf clopens a b)
  map_top' := congrArg (fun c : Clopens (Space B) => (c : Set (Space B))) (map_top clopens)
  map_bot' := congrArg (fun c : Clopens (Space B) => (c : Set (Space B))) (map_bot clopens)

@[simp] theorem toSets_apply (b : B) : toSets b = (clopens b : Set (Space B)) := rfl

theorem isTopologicalBasis_clopens :
    IsTopologicalBasis (Set.range fun b : B => (clopens b : Set (Space B))) := by
  simp only [coe_clopens]
  convert PrimeSpectrum.isTopologicalBasis_basic_opens (R := AsBoolRing B) using 1
  ext s
  exact ⟨fun ⟨b, hb⟩ => ⟨toBoolRing b, hb⟩,
    fun ⟨r, hr⟩ => ⟨ofBoolRing r, by simpa only [toBoolRing_ofBoolRing] using hr⟩⟩

instance instTotallySeparatedSpace : TotallySeparatedSpace (Space B) := by
  apply totallySeparatedSpace_of_t0_of_basis_clopen
  apply (isTopologicalBasis_clopens (B := B)).isTopologicalBasis_of_exists_subset
  · exact fun _ h => h.isOpen
  · rintro _ ⟨b, rfl⟩ x hx
    exact ⟨_, (clopens b).2, hx, Set.Subset.rfl⟩

instance instNonempty [Nontrivial B] : Nonempty (Space B) := by
  let : Nontrivial (AsBoolRing B) := toBoolRing.injective.nontrivial
  infer_instance

instance instSecondCountableTopology [Countable B] : SecondCountableTopology (Space B) :=
  isTopologicalBasis_clopens.secondCountableTopology (Set.countable_range _)

/-- The inverse-image map on points induced by a bounded lattice homomorphism. -/
def comap (f : BoundedLatticeHom B C) : C(Space C, Space B) :=
  ⟨PrimeSpectrum.comap f.asBoolRing, PrimeSpectrum.continuous_comap _⟩

@[simp] theorem preimage_clopens (f : BoundedLatticeHom B C) (b : B) :
    comap f ⁻¹' (clopens b : Set (Space B)) = clopens (f b) := rfl

/-- A Boolean order isomorphism induces a homeomorphism of its Stone spaces. -/
noncomputable def homeomorph (e : B ≃o C) : Space B ≃ₜ Space C :=
  PrimeSpectrum.homeomorphOfRingEquiv
    (RingEquiv.ofBijective (e : BoundedLatticeHom B C).asBoolRing e.bijective)

@[simp] theorem preimage_homeomorph_symm_clopens (e : B ≃o C) (b : B) :
    (homeomorph e).symm ⁻¹' (clopens b : Set (Space B)) = clopens (e b) := rfl

@[simp] theorem preimage_homeomorph_clopens (e : B ≃o C) (c : C) :
    homeomorph e ⁻¹' (clopens c : Set (Space C)) = clopens (e.symm c) := by
  calc
    _ = homeomorph e ⁻¹' ((homeomorph e).symm ⁻¹' (clopens (e.symm c) : Set (Space B))) := by
      rw [preimage_homeomorph_symm_clopens, e.apply_symm_apply]
    _ = _ := by rw [Set.preimage_preimage]; simp

/-- A family of Boolean automorphisms acts jointly continuously on the Stone space if
inverse evaluation at each Boolean element is continuous into the discrete algebra. -/
theorem continuous_homeomorph {G : Type*} [TopologicalSpace G] (e : G → B ≃o B)
    (he : ∀ b c : B, IsOpen {g | (e g).symm b = c}) :
    Continuous (fun p : G × Space B => homeomorph (e p.1) p.2) := by
  apply isTopologicalBasis_clopens.continuous_iff.mpr
  rintro _ ⟨b, rfl⟩
  have hpre : (fun p : G × Space B => homeomorph (e p.1) p.2) ⁻¹'
      (clopens b : Set (Space B)) = ⋃ c : B, {g | (e g).symm b = c} ×ˢ
        (clopens c : Set (Space B)) := by
    ext p
    change p.2 ∈ homeomorph (e p.1) ⁻¹' (clopens b : Set (Space B)) ↔ _
    rw [preimage_homeomorph_clopens]
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨c, hc, h⟩ => hc ▸ h⟩
  rw [hpre]
  exact isOpen_iUnion fun c => (he b c).prod (clopens c).isOpen

end SuccessorTree.NonPrecompact.BooleanSpectrum
