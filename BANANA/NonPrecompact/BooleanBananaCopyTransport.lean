import BANANA.NonPrecompact.BooleanBananaCopySystem
import BANANA.NonPrecompact.PrebananaFiniteBooleanModelStrongAP
import BANANA.NonPrecompact.PrebananaAbstractCodeEquivalence
import BANANA.NonPrecompact.PrebananaAbstractCodeOperations

/-!
# Transport of Boolean–BANANA persistent colourings to native copies

The atom-coordinate proof colours an unordered partition into two blocks
by orienting it with one distinguished ambient atom. Here the inverse image
of the partition under the canonical atom representation is a copy on the
original Boolean carrier. The distinguished ambient atom serves only to
choose its orientation.
-/

namespace SuccessorTree.NonPrecompact

/-- The Boolean model of the all-marked structure on `2^(k+1)` atoms. -/
def booleanBananaAllMarkedPower (k : ℕ) : PrebananaFiniteBooleanModel :=
  prebananaAtomFiniteBooleanModel (PrebananaAtomStructure.allMarkedPower k)

private noncomputable abbrev atomCode (C : PrebananaFiniteBooleanModel) :
    PrebananaAtomStructure :=
  prebananaAbstractAtomCode C.carrier C.μ C.μ_bot C.μ_top C.μ_add

private noncomputable abbrev elementCode (C : PrebananaFiniteBooleanModel) :
    C.carrier → Finset (Fin (atomCode C).atomCount) :=
  prebananaAbstractBooleanCode C.carrier

private theorem elementCode_bijective (C : PrebananaFiniteBooleanModel) :
    Function.Bijective (elementCode C) :=
  prebananaAbstractBooleanCode_bijective C.carrier

private theorem elementCode_mark (C : PrebananaFiniteBooleanModel) (x : C.carrier) :
    prebananaBooleanParity (atomCode C) (elementCode C x) = C.μ x :=
  prebananaAbstractBooleanCode_parity C.carrier C.μ C.μ_bot C.μ_top C.μ_add x

private theorem exists_encodedEmbedding {D : PrebananaAtomStructure}
    {C : PrebananaFiniteBooleanModel}
    (f : PrebananaFiniteBooleanEmbedding (prebananaAtomFiniteBooleanModel D) C) :
    ∃ g : PrebananaAtomEmbedding D (atomCode C),
      ∀ s, elementCode C (f.hom s) = prebananaBooleanMap g s := by
  classical
  let F (s : Finset (Fin D.atomCount)) := elementCode C (f.hom s)
  have hbot : F ∅ = ∅ :=
    (congrArg (elementCode C) (map_bot f.hom)).trans
      (prebananaAbstractBooleanCode_bot C.carrier)
  have htop : F Finset.univ = Finset.univ :=
    (congrArg (elementCode C) (map_top f.hom)).trans
      (prebananaAbstractBooleanCode_top C.carrier)
  have hsup (x y : Finset (Fin D.atomCount)) : F (x ∪ y) = F x ∪ F y :=
    (congrArg (elementCode C) (f.hom.map_sup' x y)).trans
      (prebananaAbstractBooleanCode_sup C.carrier _ _)
  have hinf (x y : Finset (Fin D.atomCount)) : F (x ∩ y) = F x ∩ F y :=
    (congrArg (elementCode C) (f.hom.map_inf' x y)).trans
      (prebananaAbstractBooleanCode_inf C.carrier _ _)
  obtain ⟨part, hsurj, hpart⟩ :=
    prebanana_exists_atomPartition_of_powersetEmbedding F hbot htop hsup hinf
      ((elementCode_bijective C).1.comp f.injective)
  have hfibre (i : Fin D.atomCount) : F {i} = prebananaFiber part i := by
    rw [hpart]
    simp [prebananaFiber]
  let g : PrebananaAtomEmbedding D (atomCode C) := {
    part := part
    fibre_nonempty := fun i => by
      obtain ⟨j, hj⟩ := hsurj i
      exact ⟨j, by simp [prebananaFiber, hj]⟩
    fibre_mark_parity := fun i => by
      rw [← hfibre]
      change prebananaBooleanParity (atomCode C) (F {i}) = D.mark i
      refine (elementCode_mark C _).trans ((f.preserves_μ _).trans ?_)
      exact (prebananaMarkedCount_cast_eq_sum D.mark {i}).trans (Finset.sum_singleton _ _) }
  refine ⟨g, fun s => ?_⟩
  exact hpart s

private theorem exists_nativeEmbedding {D : PrebananaAtomStructure}
    {C : PrebananaFiniteBooleanModel} (f : PrebananaAtomEmbedding D (atomCode C)) :
    ∃ g : PrebananaFiniteBooleanEmbedding (prebananaAtomFiniteBooleanModel D) C,
      ∀ s, elementCode C (g.hom s) = prebananaBooleanMap f s := by
  classical
  let e := Equiv.ofBijective (elementCode C) (elementCode_bijective C)
  let g := fun s => e.symm (prebananaBooleanMap f s)
  have hg (s) : elementCode C (g s) = prebananaBooleanMap f s :=
    e.apply_symm_apply _
  have hbot : g ∅ = ⊥ := (elementCode_bijective C).1
    ((hg _).trans ((prebananaBooleanMap_empty f).trans
      (prebananaAbstractBooleanCode_bot C.carrier).symm))
  have htop : g Finset.univ = ⊤ := (elementCode_bijective C).1
    ((hg _).trans ((prebananaBooleanMap_univ f).trans
      (prebananaAbstractBooleanCode_top C.carrier).symm))
  have hsup (x y : Finset (Fin D.atomCount)) : g (x ∪ y) = g x ⊔ g y := by
    apply (elementCode_bijective C).1
    calc
      elementCode C (g (x ∪ y)) = prebananaBooleanMap f x ∪ prebananaBooleanMap f y :=
        (hg _).trans (prebananaBooleanMap_union f x y)
      _ = elementCode C (g x) ∪ elementCode C (g y) :=
        congrArg₂ (· ∪ ·) (hg x).symm (hg y).symm
      _ = elementCode C (g x ⊔ g y) :=
        (prebananaAbstractBooleanCode_sup C.carrier _ _).symm
  have hinf (x y : Finset (Fin D.atomCount)) : g (x ∩ y) = g x ⊓ g y := by
    apply (elementCode_bijective C).1
    calc
      elementCode C (g (x ∩ y)) = prebananaBooleanMap f x ∩ prebananaBooleanMap f y :=
        (hg _).trans (prebananaBooleanMap_inter f x y)
      _ = elementCode C (g x) ∩ elementCode C (g y) :=
        congrArg₂ (· ∩ ·) (hg x).symm (hg y).symm
      _ = elementCode C (g x ⊓ g y) :=
        (prebananaAbstractBooleanCode_inf C.carrier _ _).symm
  have hmark (s : Finset (Fin D.atomCount)) : C.μ (g s) = prebananaBooleanParity D s := by
    rw [← elementCode_mark C, hg, prebananaBooleanMap_parity]
  let G : PrebananaFiniteBooleanEmbedding (prebananaAtomFiniteBooleanModel D) C := {
    hom := {
      toFun := g
      map_bot' := hbot
      map_top' := htop
      map_sup' := hsup
      map_inf' := hinf }
    injective := e.symm.injective.comp (prebananaBooleanMap_injective f)
    preserves_μ := hmark }
  exact ⟨G, hg⟩

private def blockRange {n : ℕ} (s : Finset (Fin n)) : Set (Finset (Fin n)) :=
  {∅, Finset.univ, s, Finset.univ \ s}

private theorem twoFinset_cases :
    ∀ (i : Fin 2) (s : Finset (Fin 2)),
      s = ∅ ∨ s = Finset.univ ∨ s = {i} ∨ s = Finset.univ \ {i} := by
  decide

private theorem twoFinset_compl_singleton :
    ∀ i : Fin 2, ({1 - i} : Finset (Fin 2)) = Finset.univ \ {i} := by
  decide

private theorem twoAtom_range {D : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding (PrebananaAtomStructure.allMarkedPower 0) D) (i : Fin 2) :
    Set.range (prebananaBooleanMap f) = blockRange (prebananaBooleanMap f {i}) := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    simp only [blockRange, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases twoFinset_cases i s with rfl | rfl | rfl | rfl
    · exact Or.inl (prebananaBooleanMap_empty f)
    · exact Or.inr (Or.inl (prebananaBooleanMap_univ f))
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (prebananaBooleanMap_complement f {i})))
  · intro hx
    simp only [blockRange, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨∅, prebananaBooleanMap_empty f⟩
    · exact ⟨Finset.univ, prebananaBooleanMap_univ f⟩
    · exact ⟨{i}, rfl⟩
    · exact ⟨Finset.univ \ {i}, prebananaBooleanMap_complement f {i}⟩

private theorem odd_marked_singleton_image {D : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding (PrebananaAtomStructure.allMarkedPower 0) D) (i : Fin 2) :
    Odd (prebananaMarkedCount D.mark (prebananaBooleanMap f {i})) := by
  apply ZMod.natCast_eq_one_iff_odd.mp
  have h := prebananaBooleanMap_parity f ({i} : Finset (Fin 2))
  change (prebananaMarkedCount D.mark _ : F2) =
    (prebananaMarkedCount (fun _ : Fin 2 => 1) {i} : F2) at h
  rw [prebananaMarkedCount_cast_eq_sum (fun _ : Fin 2 => (1 : F2)) {i},
    Finset.sum_singleton] at h
  exact h

private theorem mainBlock_unique {D : PrebananaAtomStructure}
    (P Q : PrebananaTwoMarkedCopy D) (h : blockRange P.block = blockRange Q.block) : P = Q := by
  have hmem : P.block ∈ blockRange Q.block := by rw [← h]; simp [blockRange]
  simp only [blockRange, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with he | he | he | he
  · have hp := P.cstar_mem
    simp [he] at hp
  · have hp := P.complement_marked_odd
    simp [he, prebananaMarkedCount] at hp
  · cases P
    cases Q
    cases he
    rfl
  · have hp := P.cstar_mem
    simp [he, Q.cstar_mem] at hp

private theorem exists_orientedBlock {D : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding (PrebananaAtomStructure.allMarkedPower 0) D) :
    ∃ P : PrebananaTwoMarkedCopy D, Set.range (prebananaBooleanMap f) = blockRange P.block := by
  let i : Fin 2 := f.part D.zeroAtom
  let s := prebananaBooleanMap f {i}
  have hcomp : prebananaBooleanMap f ({1 - i} : Finset (Fin 2)) = Finset.univ \ s :=
    (congrArg (fun t : Finset (Fin 2) => prebananaBooleanMap f t)
      (twoFinset_compl_singleton i)).trans (prebananaBooleanMap_complement f {i})
  refine ⟨⟨s, ?_, odd_marked_singleton_image f i, ?_⟩, twoAtom_range f i⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton_self _⟩
  · rw [← hcomp]
    exact odd_marked_singleton_image f (1 - i)

private theorem exists_embedding_of_orientedBlock {D : PrebananaAtomStructure}
    (P : PrebananaTwoMarkedCopy D) :
    ∃ f : PrebananaAtomEmbedding (PrebananaAtomStructure.allMarkedPower 0) D,
      Set.range (prebananaBooleanMap f) = blockRange P.block := by
  let part : Fin D.atomCount → Fin 2 := fun x => if x ∈ P.block then 0 else 1
  have hzero : prebananaFiber part 0 = P.block := by
    ext x
    by_cases hx : x ∈ P.block <;> simp [prebananaFiber, part, hx]
  have hone : prebananaFiber part 1 = Finset.univ \ P.block := by
    ext x
    by_cases hx : x ∈ P.block <;> simp [prebananaFiber, part, hx]
  have hf (i : Fin 2) : Odd (prebananaMarkedCount D.mark (prebananaFiber part i)) := by
    fin_cases i
    · change Odd (prebananaMarkedCount D.mark (prebananaFiber part 0))
      rw [hzero]
      exact P.block_marked_odd
    · change Odd (prebananaMarkedCount D.mark (prebananaFiber part 1))
      rw [hone]
      exact P.complement_marked_odd
  let f : PrebananaAtomEmbedding (PrebananaAtomStructure.allMarkedPower 0) D := {
    part := part
    fibre_nonempty := fun i => by
      by_contra h
      have he : prebananaFiber part i = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      simpa [he, prebananaMarkedCount] using hf i
    fibre_mark_parity := fun i => (hf i).natCast_zmod_two
  }
  refine ⟨f, (twoAtom_range f 0).trans ?_⟩
  have h : prebananaBooleanMap f ({0} : Finset (Fin 2)) = P.block := by
    change (Finset.univ.filter fun x => part x ∈ ({0} : Finset (Fin 2))) = P.block
    simpa [prebananaFiber] using hzero
  exact congrArg blockRange h

private theorem exists_orientedCopy
    {C : PrebananaFiniteBooleanModel}
    (p : BooleanBananaCopy (booleanBananaAllMarkedPower 0) C) :
    ∃ P : PrebananaTwoMarkedCopy (atomCode C),
      elementCode C '' p.1 = blockRange P.block := by
  obtain ⟨f, hf⟩ := p.2
  obtain ⟨g, hg⟩ := exists_encodedEmbedding f
  obtain ⟨P, hP⟩ := exists_orientedBlock g
  refine ⟨P, ?_⟩
  rw [← hf, ← Set.range_comp, ← hP]
  exact congrArg Set.range (funext hg)

private noncomputable def orientedCopy {C : PrebananaFiniteBooleanModel}
    (p : BooleanBananaCopy (booleanBananaAllMarkedPower 0) C) :
    PrebananaTwoMarkedCopy (atomCode C) :=
  Classical.choose (exists_orientedCopy p)

private theorem orientedCopy_spec {C : PrebananaFiniteBooleanModel}
    (p : BooleanBananaCopy (booleanBananaAllMarkedPower 0) C) :
    elementCode C '' p.1 = blockRange (orientedCopy p).block :=
  Classical.choose_spec (exists_orientedCopy p)

private theorem exists_copy_of_orientedBlock {C : PrebananaFiniteBooleanModel}
    (P : PrebananaTwoMarkedCopy (atomCode C)) :
    ∃ p : BooleanBananaCopy (booleanBananaAllMarkedPower 0) C,
      elementCode C '' p.1 = blockRange P.block := by
  obtain ⟨f, hf⟩ := exists_embedding_of_orientedBlock P
  obtain ⟨g, hg⟩ := exists_nativeEmbedding (C := C) f
  refine ⟨BooleanBananaCopy.ofEmbedding g, ?_⟩
  change elementCode C '' Set.range g.hom = blockRange P.block
  rw [← Set.range_comp, ← hf]
  exact congrArg Set.range (funext hg)

private theorem blockRange_subset_map {B D : PrebananaAtomStructure}
    (f : PrebananaAtomEmbedding B D) (s : Finset (Fin B.atomCount)) :
    blockRange (prebananaBooleanMap f s) ⊆ Set.range (prebananaBooleanMap f) := by
  intro x hx
  simp only [blockRange, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨∅, prebananaBooleanMap_empty f⟩
  · exact ⟨Finset.univ, prebananaBooleanMap_univ f⟩
  · exact Set.mem_range_self s
  · exact ⟨Finset.univ \ s, prebananaBooleanMap_complement f s⟩

/-- For each finite Boolean–BANANA ambient structure, a single colouring
of the two-marked-atom copy ranges exhibits every colour in every copy
of the all-marked model on `2^(k+1)` atoms. -/
theorem exists_booleanBananaPersistentColouring (k : ℕ)
    (C : PrebananaFiniteBooleanModel) :
    ∃ colouring : BooleanBananaCopy (booleanBananaAllMarkedPower 0) C → Fin (2 ^ k),
      ∀ f : PrebananaFiniteBooleanEmbedding (booleanBananaAllMarkedPower k) C,
        ∀ colour : Fin (2 ^ k),
          ∃ p : BooleanBananaCopy (booleanBananaAllMarkedPower 0) C,
            colouring p = colour ∧ p.1 ⊆ Set.range f.hom := by
  let D := atomCode C
  let _ : NeZero D.atomCount := ⟨Nat.ne_of_gt D.atomCount_pos⟩
  obtain ⟨c, hc⟩ := exists_prebananaPersistentColouring k D.mark
  refine ⟨fun p => c (orientedCopy p), ?_⟩
  intro f colour
  obtain ⟨g, hg⟩ := exists_encodedEmbedding f
  obtain ⟨P, hP, s, hs⟩ := hc (g.toAllMarkedTargetCopy k) colour
  obtain ⟨p, hp⟩ := exists_copy_of_orientedBlock (C := C) P
  have horient := mainBlock_unique (orientedCopy p) P ((orientedCopy_spec p).symm.trans hp)
  refine ⟨p, (congrArg c horient).trans hP, ?_⟩
  intro x hx
  have hmem : elementCode C x ∈ blockRange P.block :=
    hp ▸ Set.mem_image_of_mem (elementCode C) hx
  change P.block = prebananaBooleanMap g s at hs
  rw [hs] at hmem
  obtain ⟨y, hy⟩ := blockRange_subset_map g s hmem
  exact ⟨y, (elementCode_bijective C).1 ((hg y).trans hy)⟩

/-- The two-marked-atom source has infinite copy Ramsey degree in the native
Boolean–BANANA copy system. -/
theorem booleanBananaTwoMarkedCopyRamseyDegree_infinite (t : ℕ) :
    ¬ booleanBananaCopySystem.CopyRamseyDegreeLE (booleanBananaAllMarkedPower 0) t := by
  classical
  intro h
  obtain ⟨C, hC⟩ := h (booleanBananaAllMarkedPower t) (2 ^ t) (by positivity)
  obtain ⟨colouring, hcolouring⟩ := exists_booleanBananaPersistentColouring t C
  obtain ⟨f, hf⟩ := hC colouring
  let _ := booleanBananaCopySystem.copyFintype
    (booleanBananaAllMarkedPower 0) (booleanBananaAllMarkedPower t)
  have hall : booleanBananaCopySystem.coloursInside colouring f = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro colour
    obtain ⟨p, hp, hsub⟩ := hcolouring f colour
    obtain ⟨q, hq⟩ := (booleanBananaCopySystem.subcopy_range_iff f p).mp hsub
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, by rw [hq, hp]⟩
  rw [hall, Finset.card_univ, Fintype.card_fin] at hf
  exact t.lt_two_pow_self.not_ge hf

/-- Boolean–BANANA has no precompact Ramsey expansion, with hereditary
restriction and the embedding Ramsey property expressed by the shared
Ramsey expansion interface. -/
theorem booleanBanana_noPrecompactRamseyExpansion :
    ¬ Nonempty (RamseyExpansion booleanBananaCopySystem) := by
  rintro ⟨E⟩
  exact booleanBananaTwoMarkedCopyRamseyDegree_infinite _
    (E.copyRamseyDegreeLE_card_expansionTypes _)

end SuccessorTree.NonPrecompact
