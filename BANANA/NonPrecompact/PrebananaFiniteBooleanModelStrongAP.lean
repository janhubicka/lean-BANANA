import BANANA.NonPrecompact.PrebananaAbstractClassEPPA
import BANANA.NonPrecompact.PrebananaAbstractStrongAmalgamation

/-!
# Finite marked Boolean strong amalgamation in the class-level interface

This packages the existing abstract finite strong-amalgamation theorem
in the same concrete model and embedding types used by the class-level
EPPA obstruction. The amalgam is the finite marked Boolean algebra of
subsets of a finite atom set.

The common-image intersection is exact, not merely an amalgamation
of underlying carriers. No countable Fraisse limit or topological
dynamics theorem is asserted.
-/

namespace SuccessorTree.NonPrecompact

/-- View a finite marked atom set as an actual finite Boolean-algebra
carrier, with the parity of marked atoms as its additive marking. -/
def prebananaAtomFiniteBooleanModel
    (D : PrebananaAtomStructure) : PrebananaFiniteBooleanModel where
  carrier := Finset (Fin D.atomCount)
  booleanAlgebra := inferInstance
  finite := inferInstance
  nontrivial := by
    classical
    letI : Nonempty (Fin D.atomCount) := ⟨D.zeroAtom⟩
    infer_instance
  μ := prebananaBooleanParity D
  μ_bot := prebananaBooleanParity_empty D
  μ_top := prebananaBooleanParity_univ D
  μ_add := by
    intro x y hxy
    change prebananaBooleanParity D (x ∪ y) =
      prebananaBooleanParity D x + prebananaBooleanParity D y
    exact prebananaBooleanParity_union_disjoint D x y
      (Finset.disjoint_iff_inter_eq_empty.mpr hxy)

/-- Upgrade an injective parity-preserving finite Boolean map from the
algebraic amalgamation construction to an embedding of marked models. -/
def PrebananaMarkedFiniteMap.toFiniteBooleanEmbedding
    {A : PrebananaFiniteBooleanModel}
    {D : PrebananaAtomStructure}
    (h : PrebananaMarkedFiniteMap A.carrier D A.μ) :
    PrebananaFiniteBooleanEmbedding A (prebananaAtomFiniteBooleanModel D) where
  hom := {
    toFun := h.toFun
    map_bot' := h.map_bot
    map_top' := h.map_top
    map_sup' := h.map_sup
    map_inf' := h.map_inf
  }
  injective := h.injective
  preserves_μ := h.map_parity

/-- The class of all nontrivial finite Boolean algebras equipped with
an admissible additive F₂ marking has strong amalgamation for actual
marked bounded-lattice embeddings. The two images meet precisely in
the common base image. -/
theorem prebananaFiniteBooleanModel_strongAmalgamation
    (A B C : PrebananaFiniteBooleanModel)
    (f : PrebananaFiniteBooleanEmbedding A B)
    (g : PrebananaFiniteBooleanEmbedding A C) :
    ∃ D : PrebananaFiniteBooleanModel,
      ∃ i : PrebananaFiniteBooleanEmbedding B D,
      ∃ j : PrebananaFiniteBooleanEmbedding C D,
        (∀ a : A.carrier, i.hom (f.hom a) = j.hom (g.hom a)) ∧
        (∀ b : B.carrier, ∀ c : C.carrier,
          i.hom b = j.hom c →
          ∃ a : A.carrier, f.hom a = b ∧ g.hom a = c) := by
  classical
  obtain ⟨D, FB, FC, hcomm, hinter⟩ :=
    prebananaAbstractFiniteStrongAmalgamation
      A.carrier B.carrier C.carrier
      A.μ B.μ C.μ
      A.μ_bot A.μ_top A.μ_add
      B.μ_bot B.μ_top B.μ_add
      C.μ_bot C.μ_top C.μ_add
      f.hom g.hom
      f.injective (map_bot f.hom) (map_top f.hom)
      (fun x y => map_sup f.hom x y)
      (fun x y => map_inf f.hom x y)
      f.preserves_μ
      g.injective (map_bot g.hom) (map_top g.hom)
      (fun x y => map_sup g.hom x y)
      (fun x y => map_inf g.hom x y)
      g.preserves_μ
  refine ⟨prebananaAtomFiniteBooleanModel D,
    FB.toFiniteBooleanEmbedding, FC.toFiniteBooleanEmbedding, ?_, ?_⟩
  · exact hcomm
  · exact hinter

end SuccessorTree.NonPrecompact
