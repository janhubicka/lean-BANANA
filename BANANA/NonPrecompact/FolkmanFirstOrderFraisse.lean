import BANANA.NonPrecompact.FolkmanFirstOrderSubstructure
import BANANA.NonPrecompact.FolkmanNativeCompleteFiniteClass
import Mathlib.ModelTheory.Fraisse
import BANANA.NonPrecompact.FolkmanFirstOrderClass

/-!
# The first-order Folkman Fraïssé class

The native finite class is presented by its countable family of atom codes.
The first-order class consists of all structures isomorphic to those
representatives. Heredity and the embedding diagrams are transferred from
the two original non-unital sorts.
-/

namespace SuccessorTree.NonPrecompact

open FirstOrder CategoryTheory
open scoped FirstOrder

private local instance (α : Type*) [Fintype α] : Fintype (AsBoolAlg α) :=
  Fintype.ofEquiv α toBoolAlg

theorem folkmanProductBundle_mem
    {L R : Type} [BooleanRing L] [BooleanRing R] [Fintype L] [Fintype R]
    (P : FolkmanNativeFinitePairing L R) :
    folkmanProductBundle P ∈ folkmanFirstOrderClass := by
  obtain ⟨A, ⟨e⟩⟩ := folkmanNativeFiniteClass_countable_representatives P
  let e' : folkmanProductBundle P ↪[folkmanLanguage] folkmanFirstOrderRepresentative A :=
    folkmanProductEmbedding P.pairing (folkmanNativeCodeRealisation A).pairing
      e.left.toNonUnitalRingHom e.right.toNonUnitalRingHom
      e.left.injective e.right.injective e.preserves_pairing
  exact ⟨A, ⟨{
    toEquiv := e.left.toEquiv.prodCongr e.right.toEquiv
    map_fun' := e'.map_fun
    map_rel' := e'.map_rel }⟩⟩

private theorem folkmanFirstOrderClass_equiv_mem
    {M N : Bundled.{0} folkmanLanguage.Structure} (e : M ≃[folkmanLanguage] N)
    (hN : N ∈ folkmanFirstOrderClass) : M ∈ folkmanFirstOrderClass := by
  obtain ⟨A, ⟨f⟩⟩ := hN
  exact ⟨A, ⟨f.comp e⟩⟩

private theorem folkmanProductBundle_substructure_mem
    {L R : Type} [BooleanRing L] [BooleanRing R] [Fintype L] [Fintype R]
    (P : FolkmanNativeFinitePairing L R)
    (S : folkmanLanguage.Substructure (folkmanProductBundle P)) :
    (⟨↥S, Language.Substructure.inducedStructure⟩ : Bundled.{0} folkmanLanguage.Structure) ∈
      folkmanFirstOrderClass := by
  classical
  let SL := folkmanProductSubstructureLeft P.pairing S
  let SR := folkmanProductSubstructureRight P.pairing S
  letI : Fintype SL := Fintype.ofFinite _
  letI : Fintype SR := Fintype.ofFinite _
  letI := folkmanNativeSubringBooleanRing SL
  letI := folkmanNativeSubringBooleanRing SR
  let Q := folkmanNativeFiniteRestriction P SL SR
  let e : folkmanProductBundle Q ≃[folkmanLanguage] S :=
    folkmanProductSubstructureEquiv P.pairing S
  exact folkmanFirstOrderClass_equiv_mem (e := e.symm) (folkmanProductBundle_mem Q)

private theorem folkmanFirstOrderClass_hereditary : Language.Hereditary folkmanFirstOrderClass := by
  intro M hM N hN
  obtain ⟨A, ⟨e⟩⟩ := hM
  obtain ⟨_, ⟨f⟩⟩ := hN
  let g := e.toEmbedding.comp f
  have h := folkmanProductBundle_substructure_mem (folkmanNativeCodeRealisation A) g.toHom.range
  exact folkmanFirstOrderClass_equiv_mem (e := g.equivRange) h

private theorem folkmanFirstOrderClass_jointEmbedding :
    Language.JointEmbedding folkmanFirstOrderClass := by
  classical
  rintro M ⟨A, ⟨e⟩⟩ N ⟨B, ⟨f⟩⟩
  let P := folkmanNativeCodeRealisation A
  let Q := folkmanNativeCodeRealisation B
  obtain ⟨S⟩ := (show Nonempty (FolkmanNativeStrongAmalgamCertificate
    (0 : PUnit.{1} →ₙ+* _) (0 : PUnit.{1} →ₙ+* _)
    (0 : PUnit.{1} →ₙ+* _) (0 : PUnit.{1} →ₙ+* _)
    P.pairing Q.pairing) from folkmanNativeFinitePairing_joint_embedding P Q)
  let a : folkmanFirstOrderRepresentative A ↪[folkmanLanguage] folkmanProductBundle S.nativePairing :=
    folkmanProductEmbedding P.pairing S.nativePairing.pairing S.embedBLeft S.embedBRight
      S.embedBLeft_injective S.embedBRight_injective S.native_preserves_pairing_B
  let b : folkmanFirstOrderRepresentative B ↪[folkmanLanguage] folkmanProductBundle S.nativePairing :=
    folkmanProductEmbedding Q.pairing S.nativePairing.pairing S.embedCLeft S.embedCRight
      S.embedCLeft_injective S.embedCRight_injective S.native_preserves_pairing_C
  exact ⟨folkmanProductBundle S.nativePairing, folkmanProductBundle_mem _,
    ⟨a.comp e.toEmbedding⟩, ⟨b.comp f.toEmbedding⟩⟩

private theorem folkmanFirstOrderClass_amalgamation :
    Language.Amalgamation folkmanFirstOrderClass := by
  classical
  rintro M N T f g ⟨A, ⟨i⟩⟩ ⟨B, ⟨j⟩⟩ ⟨C, ⟨k⟩⟩
  let P := folkmanNativeCodeRealisation A
  let Q := folkmanNativeCodeRealisation B
  let R := folkmanNativeCodeRealisation C
  let f' := (j.toEmbedding.comp f).comp i.symm.toEmbedding
  let g' := (k.toEmbedding.comp g).comp i.symm.toEmbedding
  let a := (folkmanNativePairingEmbeddingEquiv P Q).symm f'
  let b := (folkmanNativePairingEmbeddingEquiv P R).symm g'
  obtain ⟨S⟩ := folkmanNativeFinitePairing_strong_amalgamation
    a.left b.left a.right b.right
    a.left_injective b.left_injective a.right_injective b.right_injective P Q R
    a.preserves_pairing b.preserves_pairing
  let fS : folkmanFirstOrderRepresentative B ↪[folkmanLanguage] folkmanProductBundle S.nativePairing :=
    folkmanProductEmbedding Q.pairing S.nativePairing.pairing S.embedBLeft S.embedBRight
      S.embedBLeft_injective S.embedBRight_injective S.native_preserves_pairing_B
  let gS : folkmanFirstOrderRepresentative C ↪[folkmanLanguage] folkmanProductBundle S.nativePairing :=
    folkmanProductEmbedding R.pairing S.nativePairing.pairing S.embedCLeft S.embedCRight
      S.embedCLeft_injective S.embedCRight_injective S.native_preserves_pairing_C
  refine ⟨folkmanProductBundle S.nativePairing, fS.comp j.toEmbedding, gS.comp k.toEmbedding,
    folkmanProductBundle_mem _, ?_⟩
  apply Language.Embedding.ext
  intro x
  have hfx : f' (i x) = j (f x) := by simp [f']
  have hgx : g' (i x) = k (g x) := by simp [g']
  change fS (j (f x)) = gS (k (g x))
  rw [← hfx, ← hgx]
  have ha : (folkmanNativePairingEmbeddingEquiv P Q) a = f' := Equiv.apply_symm_apply _ _
  have hb : (folkmanNativePairingEmbeddingEquiv P R) b = g' := Equiv.apply_symm_apply _ _
  rw [← ha, ← hb]
  exact Prod.ext (S.native_base_commutes_left (i x).1)
    (S.native_base_commutes_right (i x).2)

/-- The encoded native finite Folkman class satisfies mathlib's Fraïssé
class interface. The native certificate separately records strong AP. -/
theorem folkmanFirstOrderClass_isFraisse : Language.IsFraisse folkmanFirstOrderClass where
  is_nonempty := by
    let A : FolkmanAtomStructure := ⟨0, 0, fun x _ => Fin.elim0 x⟩
    exact ⟨folkmanFirstOrderRepresentative A, folkmanFirstOrderRepresentative_mem A⟩
  FG := by
    rintro M ⟨A, ⟨e⟩⟩
    letI : Finite M := Finite.of_injective e e.injective
    exact Language.Structure.FG.of_finite
  is_essentially_countable := by
    apply (Set.countable_range (fun A : FolkmanAtomStructure =>
      Quotient.mk' (s := Language.equivSetoid) (folkmanFirstOrderRepresentative A))).mono
    rintro _ ⟨M, ⟨A, ⟨e⟩⟩, rfl⟩
    exact ⟨A, Quotient.sound ⟨e.symm⟩⟩
  hereditary := folkmanFirstOrderClass_hereditary
  jointEmbedding := folkmanFirstOrderClass_jointEmbedding
  amalgamation := folkmanFirstOrderClass_amalgamation

end SuccessorTree.NonPrecompact
