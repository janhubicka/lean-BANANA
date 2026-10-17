import BANANA.NonPrecompact.PrebananaCountableMarkedBooleanModel
import Mathlib.Order.BooleanSubalgebra

/-!
# One-point extension in locally finite countable marked Boolean algebras

The back-and-forth proof of ultrahomogeneity rests on a generic
finite-domain argument, independent of the explicit five-ary cylinders.

Assume that finite families of the ambient marked Boolean algebra
are contained in finite Boolean subalgebras, and that every prescribed
finite marked embedding extends along every finite marked extension.
Given two embeddings of the same finite marked algebra, one may
extend the first embedding's finite source by a specified new point,
while extending the second embedding to the same larger domain.

The result is a one-sided finite marked partial-isomorphism extension
certificate. No global automorphism or ultrahomogeneity is asserted.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Every finite family of elements lies in a finite Boolean
subalgebra of the ambient countable marked Boolean model. -/
def PrebananaCountableBooleanModel.HasFiniteAmbients
    (M : PrebananaCountableBooleanModel) : Prop :=
  ∀ (xs : Finset M.carrier),
    ∃ S : BooleanSubalgebra M.carrier,
      Finite S ∧ ∀ x ∈ xs, x ∈ S

/-- The finite marked extension property for an arbitrary
countable marked Boolean model. -/
def PrebananaCountableBooleanModel.HasFiniteExtensionProperty
    (M : PrebananaCountableBooleanModel) : Prop :=
  ∀ (A B : PrebananaFiniteBooleanModel)
    (f : PrebananaFiniteBooleanEmbedding A B)
    (e : PrebananaFiniteToCountableEmbedding A M),
    ∃ h : PrebananaFiniteToCountableEmbedding B M,
      ∀ a : A.carrier, h.hom (f.hom a) = e.hom a

/-- A finite Boolean subalgebra of an arbitrary countable marked
Boolean model inherits the admissible F₂ marking. -/
noncomputable def PrebananaCountableBooleanModel.finiteSubmodel
    (M : PrebananaCountableBooleanModel)
    (S : BooleanSubalgebra M.carrier) [Finite S] :
    PrebananaFiniteBooleanModel where
  carrier := S
  booleanAlgebra := inferInstance
  finite := Fintype.ofFinite S
  nontrivial := by
    refine ⟨(⊥ : S), (⊤ : S), ?_⟩
    intro h
    have hval : (⊥ : M.carrier) = ⊤ :=
      congrArg Subtype.val h
    exact (bot_ne_top : (⊥ : M.carrier) ≠ ⊤) hval
  μ := fun x => M.μ x.val
  μ_bot := M.μ_bot
  μ_top := M.μ_top
  μ_add := by
    intro x y hxy
    change M.μ (x.val ⊔ y.val) = M.μ x.val + M.μ y.val
    exact M.μ_add x.val y.val (congrArg Subtype.val hxy)

/-- The inclusion of a finite Boolean subalgebra is a genuine
marking-preserving finite-to-countable embedding. -/
noncomputable def PrebananaCountableBooleanModel.finiteSubmodelEmbedding
    (M : PrebananaCountableBooleanModel)
    (S : BooleanSubalgebra M.carrier) [Finite S] :
    PrebananaFiniteToCountableEmbedding (M.finiteSubmodel S) M where
  hom := S.subtype
  injective := Subtype.val_injective
  preserves_μ := by intro x; rfl

/-- Generic one-point forth step: include a new source point in a
finite marked ambient structure and extend the prescribed map into
the target model along that entire finite extension.

The first embedding `j` specifies the current finite source domain,
and `e` specifies how it is matched in the target model. The
conclusion contains both an inclusion `i` of an enlarged finite
domain (including `x`) and a matching marked embedding `h`
into the target model. No bijective global extension is asserted. -/
theorem PrebananaCountableBooleanModel.onePointForth
    (M : PrebananaCountableBooleanModel)
    (hfinite : M.HasFiniteAmbients)
    (hext : M.HasFiniteExtensionProperty)
    (A : PrebananaFiniteBooleanModel)
    (j e : PrebananaFiniteToCountableEmbedding A M)
    (x : M.carrier) :
    ∃ B : PrebananaFiniteBooleanModel,
      ∃ f : PrebananaFiniteBooleanEmbedding A B,
      ∃ i h : PrebananaFiniteToCountableEmbedding B M,
      ∃ y : B.carrier,
        i.hom y = x ∧
        (∀ a : A.carrier, i.hom (f.hom a) = j.hom a) ∧
        (∀ a : A.carrier, h.hom (f.hom a) = e.hom a) := by
  classical
  let xs : Finset M.carrier :=
    (Finset.univ.image (fun a : A.carrier => j.hom a)).insert x
  obtain ⟨S, hSfinite, hS⟩ := hfinite xs
  have hjS (a : A.carrier) : j.hom a ∈ S := by
    apply hS
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hxS : x ∈ S := hS x (Finset.mem_insert_self x _)
  letI : Finite S := hSfinite
  let B : PrebananaFiniteBooleanModel := M.finiteSubmodel S
  let i : PrebananaFiniteToCountableEmbedding B M :=
    M.finiteSubmodelEmbedding S
  let f : PrebananaFiniteBooleanEmbedding A B := {
    hom := {
      toFun := fun a => ⟨j.hom a, hjS a⟩
      map_bot' := by
        apply Subtype.ext
        exact map_bot j.hom
      map_top' := by
        apply Subtype.ext
        exact map_top j.hom
      map_sup' := by
        intro a b
        apply Subtype.ext
        exact map_sup j.hom a b
      map_inf' := by
        intro a b
        apply Subtype.ext
        exact map_inf j.hom a b
    }
    injective := by
      intro a b hab
      apply j.injective
      exact congrArg Subtype.val hab
    preserves_μ := by
      intro a
      exact j.preserves_μ a
  }
  obtain ⟨h, hh⟩ := hext A B f e
  refine ⟨B, f, i, h, ⟨x, hxS⟩, rfl, ?_, hh⟩
  intro a
  rfl

end SuccessorTree.NonPrecompact
