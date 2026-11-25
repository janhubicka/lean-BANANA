import BANANA.NonPrecompact.FolkmanFirstOrderDecodingLimit
import BANANA.NonPrecompact.FolkmanNativeOneAtom
import Mathlib.Algebra.BigOperators.Fin

/-!
# Homogeneous nonzero intervals in the Folkman limit

Non-unital embeddings of finite Boolean rings allow the whole top of a
finite code to be sent to any nonzero left element of the limit.
The pairing vanishes when the right source is the zero ring.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical symmDiff BigOperators FirstOrder
open FirstOrder CategoryTheory

section AtomSums

variable {R : Type*} [NonUnitalCommRing R] {k : ℕ}

private theorem atomSum_symmDiff (b : Fin k → R) (htwo : ∀ x : R, x + x = 0)
    (s t : Finset (Fin k)) :
    (∑ i ∈ s ∆ t, b i) = (∑ i ∈ s, b i) + ∑ i ∈ t, b i := by
  classical
  rw [symmDiff_eq_sup_sdiff_inf]
  change (∑ i ∈ (s ∪ t) \ (s ∩ t), b i) = (∑ i ∈ s, b i) + ∑ i ∈ t, b i
  calc
    _ = ((∑ i ∈ (s ∪ t) \ (s ∩ t), b i) + (∑ i ∈ s ∩ t, b i)) +
        (∑ i ∈ s ∩ t, b i) := by rw [add_assoc, htwo, add_zero]
    _ = (∑ i ∈ s ∪ t, b i) + (∑ i ∈ s ∩ t, b i) := by
      rw [Finset.sum_sdiff (show s ∩ t ⊆ s ∪ t from inf_le_sup)]
    _ = _ := Finset.sum_union_inter

/-- A family of orthogonal idempotents determines a non-unital Boolean
ring homomorphism, without any named unit in the target. -/
def folkmanAtomSumHom (b : Fin k → R) (htwo : ∀ x : R, x + x = 0)
    (hidem : ∀ i, b i * b i = b i)
    (hdisj : Pairwise (fun i j => b i * b j = 0)) :
    FolkmanNativeCodeRing k →ₙ+* R where
  toFun x := ∑ i ∈ ofBoolRing x, b i
  map_zero' := Finset.sum_empty
  map_add' x y := by
    change (∑ i ∈ ofBoolRing (x + y), b i) =
      (∑ i ∈ ofBoolRing x, b i) + ∑ i ∈ ofBoolRing y, b i
    rw [ofBoolRing_add]
    exact atomSum_symmDiff b htwo _ _
  map_mul' x y := by
    classical
    change (∑ i ∈ ofBoolRing (x * y), b i) =
      (∑ i ∈ ofBoolRing x, b i) * ∑ i ∈ ofBoolRing y, b i
    rw [ofBoolRing_mul, Finset.inf_eq_inter, Finset.sum_mul_sum]
    have h (i j : Fin k) : b i * b j = if i = j then b j else 0 := by
      by_cases hij : i = j
      · subst j; simp [hidem]
      · simp [hdisj hij, hij]
    simp_rw [h, Finset.sum_ite_eq]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter]

theorem folkmanAtomSumHom_apply_singleton (b : Fin k → R)
    (htwo : ∀ x : R, x + x = 0) (hidem : ∀ i, b i * b i = b i)
    (hdisj : Pairwise (fun i j => b i * b j = 0)) (i : Fin k) :
    folkmanAtomSumHom b htwo hidem hdisj (toBoolRing {i}) = b i := by
  change (∑ j ∈ ofBoolRing (toBoolRing ({i} : Finset (Fin k))), b j) = _
  rw [ofBoolRing_toBoolRing, Finset.sum_singleton]

theorem folkmanAtomSumHom_apply_one (b : Fin k → R)
    (htwo : ∀ x : R, x + x = 0) (hidem : ∀ i, b i * b i = b i)
    (hdisj : Pairwise (fun i j => b i * b j = 0)) :
    folkmanAtomSumHom b htwo hidem hdisj 1 = ∑ i, b i := rfl

/-- Nonzero members of the disjoint family make the atom-sum map injective. -/
theorem folkmanAtomSumHom_injective (b : Fin k → R)
    (htwo : ∀ x : R, x + x = 0) (hidem : ∀ i, b i * b i = b i)
    (hdisj : Pairwise (fun i j => b i * b j = 0)) (hne : ∀ i, b i ≠ 0) :
    Function.Injective (folkmanAtomSumHom b htwo hidem hdisj) := by
  classical
  let f := folkmanAtomSumHom b htwo hidem hdisj
  have h (x : FolkmanNativeCodeRing k) (i : Fin k) :
      b i * f x = if i ∈ ofBoolRing x then b i else 0 := by
    change b i * (∑ j ∈ ofBoolRing x, b j) = _
    rw [Finset.mul_sum]
    have hprod (j : Fin k) : b i * b j = if i = j then b j else 0 := by
      by_cases hij : i = j
      · subst j; simp [hidem]
      · simp [hdisj hij, hij]
    simp_rw [hprod, Finset.sum_ite_eq]
  intro x y hxy
  apply ofBoolRing.injective
  ext i
  have heq := (h x i).symm.trans ((congrArg (fun z => b i * z) hxy).trans (h y i))
  by_cases hx : i ∈ ofBoolRing x <;> by_cases hy : i ∈ ofBoolRing y
  · simp [hx, hy]
  · exact (hne i (by simpa [hx, hy] using heq)).elim
  · exact (hne i (by simpa [hx, hy] using heq.symm)).elim
  · simp [hx, hy]

end AtomSums

namespace FolkmanDecoding

variable (M : Bundled.{0} folkmanLanguage.Structure)
variable (hD : FactorsThroughPairedProducts M)

private theorem left_idempotent (a : leftSort M hD) : a * a = a := by
  apply Subtype.ext
  exact productRing_mul_self M hD _

private theorem left_two_torsion (a : leftSort M hD) : a + a = 0 := by
  calc
    a + a = -a + a := rfl
    _ = 0 := neg_add_cancel _

private theorem decoded_pairing_right_zero (a : leftSort M hD) :
    pairing M hD a 0 = 0 := by
  have h := pairing_add_right M hD a 0 0
  rw [add_zero] at h
  exact add_left_cancel (show pairing M hD a 0 + pairing M hD a 0 =
    pairing M hD a 0 + 0 from h.symm.trans (add_zero _).symm)

/-- Finite code with the given left atom number and the zero right ring. -/
private def leftCode (k : ℕ) : FolkmanAtomStructure :=
  ⟨k, 0, fun _ j => j.elim0⟩

private theorem zeroCode_eq_zero (y : FolkmanNativeCodeRing 0) : y = 0 := by
  apply ofBoolRing.injective
  ext i
  exact i.elim0

private theorem leftCode_pairing_zero {k : ℕ} (x : FolkmanNativeCodeRing k)
    (y : FolkmanNativeCodeRing 0) :
    (folkmanNativeCodeRealisation (leftCode k)).pairing x y = 0 := by
  change (∑ _ ∈ ofBoolRing x, ∑ j ∈ ofBoolRing y, (j.elim0 : ZMod 2)) = 0
  rw [zeroCode_eq_zero y]
  rw [ofBoolRing_zero]
  change (∑ _ ∈ ofBoolRing x, ∑ j ∈ (∅ : Finset (Fin 0)), (j.elim0 : ZMod 2)) = 0
  simp

/-- A non-unital embedding of a finite left ring yields a full native
diagram in the encoded limit, with the finite right source equal to zero. -/
private noncomputable def leftCodeEmbedding {k : ℕ}
    (f : FolkmanNativeCodeRing k →ₙ+* leftSort M hD) (hf : Function.Injective f) :
    folkmanFirstOrderRepresentative (leftCode k) ↪[folkmanLanguage] M := by
  let c := encodingEquiv M hD
  let _ := folkmanProductStructure (pairing M hD)
  exact c.symm.toEmbedding.comp (folkmanProductEmbedding
    (folkmanNativeCodeRealisation (leftCode k)).pairing (pairing M hD) f
    (0 : FolkmanNativeCodeRing 0 →ₙ+* rightSort M hD) hf
    (fun x y _ => (zeroCode_eq_zero x).trans (zeroCode_eq_zero y).symm) (by
      intro x y
      change pairing M hD (f x) 0 = _
      rw [decoded_pairing_right_zero]
      exact (leftCode_pairing_zero (k := k) x y).symm))

private theorem leftCodeEmbedding_apply {k : ℕ}
    (f : FolkmanNativeCodeRing k →ₙ+* leftSort M hD) (hf : Function.Injective f)
    (x : FolkmanNativeCodeRing k) :
    leftCodeEmbedding M hD f hf (x, 0) = (f x : M) := by
  let _ := productRing M hD
  change (f x : M) + 0 = f x
  exact add_zero _

private theorem extends_embeddings {S : Bundled.{0} folkmanLanguage.Structure} [Finite S]
    (homog : folkmanLanguage.IsUltrahomogeneous M) (f g : S ↪[folkmanLanguage] M) :
    ∃ e : M ≃[folkmanLanguage] M, ∀ z, e (f z) = g z := by
  obtain ⟨e, he⟩ := homog f.toHom.range
    (Language.Structure.FG.of_finite.range f.toHom) (g.comp f.equivRange.symm.toEmbedding)
  refine ⟨e, fun z => ?_⟩
  have h := congrArg (fun j : f.toHom.range ↪[folkmanLanguage] M =>
    j (f.equivRange z)) he
  simpa using h.symm

private theorem exists_oneAtomEmbedding (a : leftSort M hD) (ha : a ≠ 0) :
    ∃ f : FolkmanNativeCodeRing 1 →ₙ+* leftSort M hD,
      Function.Injective f ∧ f 1 = a := by
  let b : Fin 1 → leftSort M hD := fun _ => a
  have hdisj : Pairwise (fun i j => b i * b j = 0) := by
    intro i j hij
    exact (hij (Subsingleton.elim _ _)).elim
  let f := folkmanAtomSumHom b (left_two_torsion M hD)
    (fun i => left_idempotent M hD (b i)) hdisj
  refine ⟨f, folkmanAtomSumHom_injective _ _ _ _ (fun _ => ha), ?_⟩
  rw [folkmanAtomSumHom_apply_one]
  simp [b]

private theorem exists_twoAtomEmbedding (a x : leftSort M hD)
    (hx : x ≠ 0) (hxa : x ≠ a) (hbelow : x * a = x) :
    ∃ f : FolkmanNativeCodeRing 2 →ₙ+* leftSort M hD,
      Function.Injective f ∧ f 1 = a ∧ f (toBoolRing {0}) = x := by
  have hzero : x * (a + x) = 0 := by
    rw [mul_add, hbelow, left_idempotent, left_two_torsion]
  have hne : a + x ≠ 0 := by
    intro hz
    apply hxa
    calc
      x = (a + x) + a := by rw [add_right_comm, left_two_torsion, zero_add]
      _ = a := by simp [hz]
  let b : Fin 2 → leftSort M hD := ![x, a + x]
  have hdisj : Pairwise (fun i j => b i * b j = 0) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hzero
    · change (a + x) * x = 0
      rw [mul_comm]
      exact hzero
    · exact (hij rfl).elim
  have hnonzero (i : Fin 2) : b i ≠ 0 := by
    fin_cases i
    · exact hx
    · exact hne
  let f := folkmanAtomSumHom b (left_two_torsion M hD)
    (fun i => left_idempotent M hD (b i)) hdisj
  refine ⟨f, folkmanAtomSumHom_injective _ _ _ _ hnonzero, ?_, ?_⟩
  · rw [folkmanAtomSumHom_apply_one, Fin.sum_univ_two]
    change x + (a + x) = a
    rw [add_left_comm, left_two_torsion, add_zero]
  · rw [folkmanAtomSumHom_apply_singleton]
    rfl

/-- The full encoded automorphism group stabilising a nonzero left element
acts transitively on its nonzero proper subelements. Both right source rings
are zero, so no additional pairing data is needed in the finite diagrams. -/
theorem folkmanLeftInterval_stabilizer_transitive [Countable M]
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M)
    (a x y : leftSort M hD)
    (hx : x ≠ 0) (hxa : x ≠ a) (hxbelow : x * a = x)
    (hy : y ≠ 0) (hya : y ≠ a) (hybelow : y * a = y) :
    ∃ e : M ≃[folkmanLanguage] M, e a.val = a.val ∧ e x.val = y.val := by
  obtain ⟨f, hf, hft, hfx⟩ := exists_twoAtomEmbedding M hD a x hx hxa hxbelow
  obtain ⟨g, hg, hgt, hgy⟩ := exists_twoAtomEmbedding M hD a y hy hya hybelow
  obtain ⟨e, he⟩ := extends_embeddings M hM.ultrahomogeneous
    (leftCodeEmbedding M hD f hf) (leftCodeEmbedding M hD g hg)
  have act (u : FolkmanNativeCodeRing 2) : e (f u : M) = (g u : M) := by
    let z : folkmanFirstOrderRepresentative (leftCode 2) := (u, 0)
    calc
      e (f u : M) = e (leftCodeEmbedding M hD f hf z) :=
        congrArg e (leftCodeEmbedding_apply M hD f hf u).symm
      _ = leftCodeEmbedding M hD g hg z := he z
      _ = (g u : M) := leftCodeEmbedding_apply M hD g hg u
  refine ⟨e, ?_, ?_⟩
  · have ht := act 1
    rwa [hft, hgt] at ht
  · have hs := act (toBoolRing {0})
    rwa [hfx, hgy] at hs

/-- Every nonzero left element has a copy of the finite Boolean algebra
on any positive number of atoms below it. This is the finite extension
property applied to the embedding sending the single atom to the top. -/
theorem folkmanLeftElement_exists_finiteIntervalEmbedding [Countable M]
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M)
    (a : leftSort M hD) (ha : a ≠ 0) (k : ℕ) (hk : 0 < k) :
    ∃ f : FolkmanNativeCodeRing k →ₙ+* leftSort M hD,
      Function.Injective f ∧ f 1 = a := by
  obtain ⟨fa, hfa, htop⟩ := exists_oneAtomEmbedding M hD a ha
  let f := leftCodeEmbedding M hD fa hfa
  have hne : (1 : FolkmanNativeCodeRing k) ≠ 0 := by
    intro h
    have h' := congrArg ofBoolRing h
    change (Finset.univ : Finset (Fin k)) = ∅ at h'
    exact (Finset.notMem_empty (⟨0, hk⟩ : Fin k)) (h' ▸ Finset.mem_univ _)
  let g : folkmanFirstOrderRepresentative (leftCode 1) ↪[folkmanLanguage]
      folkmanFirstOrderRepresentative (leftCode k) :=
    folkmanProductEmbedding (folkmanNativeCodeRealisation (leftCode 1)).pairing
      (folkmanNativeCodeRealisation (leftCode k)).pairing
      (folkmanOneAtomHom (1 : FolkmanNativeCodeRing k)) (NonUnitalRingHom.id _)
      (folkmanOneAtomHom_injective hne) (fun _ _ h => h)
      (fun x y => (leftCode_pairing_zero _ _).trans (leftCode_pairing_zero _ _).symm)
  have hmem := folkmanFirstOrderRepresentative_mem (leftCode k)
  rw [← hM.age] at hmem
  let _ : Nonempty (folkmanFirstOrderRepresentative (leftCode k) ↪[folkmanLanguage] M) := hmem.2
  obtain ⟨f', hf'⟩ := hM.ultrahomogeneous.extend_embedding
    (Language.Structure.FG.of_finite (M := folkmanFirstOrderRepresentative (leftCode 1))) f g
  let c := encodingEquiv M hD
  let _ := folkmanProductStructure (pairing M hD)
  let e := c.toEmbedding.comp f'
  let l := folkmanProductEmbeddingLeft (folkmanNativeCodeRealisation (leftCode k)).pairing
    (pairing M hD) e
  refine ⟨l, folkmanProductEmbeddingLeft_injective _ _ e, ?_⟩
  let z : folkmanFirstOrderRepresentative (leftCode 1) := (1, 0)
  let w : folkmanFirstOrderRepresentative (leftCode k) := (1, 0)
  have hg1 : g z = w := by
    exact Prod.ext (folkmanOneAtomHom_one _) rfl
  have hfg : f z = f' w := by
    calc
      f z = (f'.comp g) z := congrArg (fun j :
          folkmanFirstOrderRepresentative (leftCode 1) ↪[folkmanLanguage] M => j z) hf'
      _ = f' w := congrArg f' hg1
  have hfa' : f' w = a.val := hfg.symm.trans
    ((leftCodeEmbedding_apply M hD fa hfa 1).trans (congrArg Subtype.val htop))
  change (c (f' w)).1 = a
  rw [hfa']
  have hca : c.symm (a, 0) = a.val := by
    let _ := productRing M hD
    change a.val + 0 = a.val
    exact add_zero _
  rw [← hca, c.apply_symm_apply]

/-- The interval below any nonzero left element admits a partition into
any positive finite number of nonzero elements. -/
theorem folkmanLeftElement_exists_partition [Countable M]
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M)
    (a : leftSort M hD) (ha : a ≠ 0) (k : ℕ) (hk : 0 < k) :
    ∃ b : Fin k → leftSort M hD,
      (∀ i, b i ≠ 0 ∧ b i * a = b i) ∧
      Pairwise (fun i j => b i * b j = 0) ∧ (∑ i, b i) = a := by
  classical
  obtain ⟨f, hf, ht⟩ := folkmanLeftElement_exists_finiteIntervalEmbedding M hD hM a ha k hk
  let singleton (i : Fin k) : FolkmanNativeCodeRing k := toBoolRing {i}
  let b (i : Fin k) := f (singleton i)
  refine ⟨b, ?_, ?_, ?_⟩
  · intro i
    constructor
    · intro h
      have he : singleton i = 0 := hf (h.trans (map_zero f).symm)
      have hs := congrArg ofBoolRing he
      change ({i} : Finset (Fin k)) = ∅ at hs
      exact Finset.notMem_empty i (hs ▸ Finset.mem_singleton_self i)
    · change f (singleton i) * a = f (singleton i)
      rw [← ht, ← map_mul, mul_one]
  · intro i j hij
    change f (singleton i) * f (singleton j) = 0
    rw [← map_mul]
    change f (toBoolRing ({i} : Finset (Fin k)) * toBoolRing {j}) = 0
    rw [← toBoolRing_inf]
    have h : ({i} : Finset (Fin k)) ⊓ {j} = ⊥ := by
      change ({i} : Finset (Fin k)) ∩ {j} = ∅
      ext z
      simp [hij]
    rw [h, toBoolRing_bot, map_zero]
  · have hsum (s : Finset (Fin k)) : (∑ i ∈ s, singleton i) = toBoolRing s := by
      induction s using Finset.induction_on with
      | empty => exact toBoolRing_bot.symm
      | @insert i s hi ih =>
        rw [Finset.sum_insert hi, ih]
        change toBoolRing ({i} : Finset (Fin k)) + toBoolRing s = _
        rw [← toBoolRing_symmDiff]
        apply congrArg toBoolRing
        ext j
        by_cases hj : j = i <;> simp [Finset.mem_symmDiff, hj, hi]
    change (∑ i, f (singleton i)) = a
    rw [← map_sum, hsum]
    exact ht

/-- The decoded left sort contains a nonzero element, since the encoded
age contains the one-atom left ring with zero right ring. -/
theorem folkmanLeftSort_exists_nonzero [Countable M]
    (hM : Language.IsFraisseLimit folkmanFirstOrderClass M) :
    ∃ a : leftSort M hD, a ≠ 0 := by
  have hmem := folkmanFirstOrderRepresentative_mem (leftCode 1)
  rw [← hM.age] at hmem
  obtain ⟨e⟩ := hmem.2
  let c := encodingEquiv M hD
  let _ := folkmanProductStructure (pairing M hD)
  let f := c.toEmbedding.comp e
  let l := folkmanProductEmbeddingLeft (folkmanNativeCodeRealisation (leftCode 1)).pairing
    (pairing M hD) f
  have hl := folkmanProductEmbeddingLeft_injective _ _ f
  refine ⟨l 1, fun h => folkmanOneAtom_one_ne_zero (hl (h.trans (map_zero l).symm))⟩

end FolkmanDecoding
end SuccessorTree.NonPrecompact
