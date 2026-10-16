import BANANA.NonPrecompact.PrebananaFiveAryTowerLongPrefix
import BANANA.NonPrecompact.PrebananaFiveAryFiniteExtensionSquare
import BANANA.NonPrecompact.PrebananaAbstractModelPowersetEmbedding

/-!
# The abstract finite-extension square from compatible atom partitions

The finite word-level allocation and the canonical atom-powerset
representation give a genuine extension of an arbitrary marked finite
Boolean embedding, provided the two atom partitions encode the given
maps on *all* Boolean elements. This is the precise integration lemma
for the upcoming extraction of those partitions from arbitrary maps.

The assumptions retain equality in each base-atom marking fibre. An
equality only of global markings is insufficient.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical BigOperators

/-- Upgrade compatible atom partitions describing both given
embeddings on all elements to a genuine commuting square of finite
marked Boolean-algebra embeddings in the actual five-ary tower. -/
theorem prebananaFiveAry_abstractExtensionFromPartitions
    (A B : PrebananaFiniteBooleanModel) (n : ℕ)
    (f : PrebananaFiniteBooleanEmbedding A B)
    (e : PrebananaFiniteBooleanEmbedding
      A (prebananaFiveAryBooleanStage n))
    (source : PrebananaFiveAryWord n →
      PrebananaAbstractAtoms A.carrier)
    (target : PrebananaAbstractAtoms B.carrier →
      PrebananaAbstractAtoms A.carrier)
    (hsource : Function.Surjective source)
    (htarget : Function.Surjective target)
    (hlocal : ∀ a : PrebananaAbstractAtoms A.carrier,
      (∑ w : PrebananaFiveAryWord n,
        if source w = a then prebananaFiveAryWordMark n w else 0) =
      ∑ b : PrebananaAbstractAtoms B.carrier,
        if target b = a then B.μ (b : B.carrier) else 0)
    (hsourceMap : ∀ x : A.carrier,
      e.hom x =
        Finset.univ.filter (fun w : PrebananaFiveAryWord n =>
          source w ∈
            prebananaFiniteBooleanAtomFinsetOrderIso A.carrier x))
    (htargetMap : ∀ x : A.carrier,
      prebananaFiniteBooleanAtomFinsetOrderIso B.carrier
        (f.hom x) =
        Finset.univ.filter
          (fun b : PrebananaAbstractAtoms B.carrier =>
            target b ∈
              prebananaFiniteBooleanAtomFinsetOrderIso A.carrier x)) :
    ∃ g : PrebananaFiniteBooleanEmbedding B
        (prebananaFiveAryBooleanStage
          (n + Fintype.card (PrebananaAbstractAtoms B.carrier))),
      ∀ x : A.carrier,
        g.hom (f.hom x) =
          (prebananaExplicitFiveAryTower.iterFrom n
            (Fintype.card (PrebananaAbstractAtoms B.carrier))).hom
            (e.hom x) := by
  classical
  let β := PrebananaAbstractAtoms B.carrier
  let δ := PrebananaAbstractAtoms A.carrier
  letI : Nonempty β := prebananaAbstractAtoms_nonempty B.carrier
  let markB : β → F2 := fun b => B.μ (b : B.carrier)
  have htotal : (∑ b : β, markB b) = 0 :=
    prebananaAbstractParity_total_even_on_atoms
      B.carrier B.μ B.μ_bot B.μ_top B.μ_add
  obtain ⟨gcoord, hcomm⟩ :=
    prebananaFiveAry_finiteExtensionSquare n β δ
      source target hsource htarget markB htotal hlocal
  let code : PrebananaFiniteBooleanEmbedding B
      (prebananaFiniteMarkedPowerset β markB htotal) :=
    prebananaAbstractModel_markedPowersetEmbedding B
  refine ⟨gcoord.comp code, ?_⟩
  intro x
  let s : Finset δ :=
    prebananaFiniteBooleanAtomFinsetOrderIso A.carrier x
  have hcode : code.hom (f.hom x) =
      Finset.univ.filter (fun b : β => target b ∈ s) := by
    change prebananaFiniteBooleanAtomFinsetOrderIso B.carrier
      (f.hom x) =
        Finset.univ.filter (fun b : β => target b ∈ s)
    exact htargetMap x
  have hext (w : PrebananaFiveAryWord n) :
      w ∈ e.hom x ↔ source w ∈ s := by
    rw [hsourceMap x]
    simp [s]
  calc
    (gcoord.comp code).hom (f.hom x) =
        gcoord.hom (code.hom (f.hom x)) := rfl
    _ = gcoord.hom
          (Finset.univ.filter (fun b : β => target b ∈ s)) := by
            rw [hcode]
    _ = Finset.univ.filter
          (fun w : PrebananaFiveAryWord (n + Fintype.card β) =>
            source
              (prebananaFiveAryLongPrefix n (Fintype.card β) w) ∈ s) :=
            hcomm s
    _ = Finset.univ.filter
          (fun w : PrebananaFiveAryWord (n + Fintype.card β) =>
            prebananaFiveAryLongPrefix n (Fintype.card β) w ∈ e.hom x) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact (hext _).symm
    _ = (prebananaExplicitFiveAryTower.iterFrom n
          (Fintype.card β)).hom (e.hom x) :=
            (prebananaFiveAryTower_iter_eq_prefix
              n (Fintype.card β) (e.hom x)).symm

end SuccessorTree.NonPrecompact
