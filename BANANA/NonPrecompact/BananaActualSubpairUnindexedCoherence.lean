import BANANA.NonPrecompact.BananaActualSubpairClassCoherence
import BANANA.NonPrecompact.CoherentGroupoidDescent

/-!
# Coherent EPPA on unindexed actual partial automorphisms of finite BANANA

The class-indexed action of BananaActualSubpairClassCoherence can be descended
to a single map on every genuine two-sorted partial isomorphism of A.

The source class is uniquely determined by the domain, and an isomorphism
identifies the source and target classes. The only required dependent cast
is an equality of quotient indices. All its proof witnesses are proposition
proofs, so they cannot affect the resulting ambient automorphism.

No nondegeneracy, positive dimension, or extra compatibility assumption is
introduced. The target witness is the SAME perfect completion B_(l+r).

All declarations here are staged and require exact-head local Lean compilation,
transitive-axiom checks and independent statement review before any merge.
-/

namespace SuccessorTree.NonPrecompact

/-- The isomorphism type of the once-chosen coordinates of an actual subpair. -/
def bananaActualSubpairClass
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U : BananaActualSubpair A) : BananaPresentedIsoClass A :=
  bananaPresentedClassOf U.presentation

/-- The class-labelled object corresponding to a fixed actual subpair. -/
def bananaActualClassObjectOf
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U : BananaActualSubpair A) :
    BananaActualClassObject A (bananaActualSubpairClass U) :=
  ⟨U, rfl⟩

/-- Changing a quotient-class label along an equality does not change
an action whose objects carry only a proof of membership in that class.
This is the dependent-transport calculation required for composition. -/
theorem bananaActualClassAction_changeIndex
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (Θ : ∀ (c : BananaPresentedIsoClass A)
        ⦃U V : BananaActualClassObject A c⦄,
      BananaActualSubpairIso U.1 V.1 →
        BananaMatrixAutGroup (perfectBanana (l + r)))
    {c d : BananaPresentedIsoClass A} (h : c = d)
    {U V : BananaActualSubpair A}
    (hU : bananaActualSubpairClass U = c)
    (hV : bananaActualSubpairClass V = c)
    (p : BananaActualSubpairIso U V) :
    Θ c (U := ⟨U, hU⟩) (V := ⟨V, hV⟩) p =
      Θ d (U := ⟨U, hU.trans h⟩) (V := ⟨V, hV.trans h⟩) p := by
  cases h
  rfl

/-- An action on each isomorphism class becomes an action on ALL actual
partial isomorphisms, by choosing the class of the source and transporting
the target membership along the isomorphism-induced equality. -/
noncomputable def bananaActualClassAction_descend
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (Θ : ∀ (c : BananaPresentedIsoClass A)
        ⦃U V : BananaActualClassObject A c⦄,
      BananaActualSubpairIso U.1 V.1 →
        BananaMatrixAutGroup (perfectBanana (l + r)))
    {U V : BananaActualSubpair A}
    (p : BananaActualSubpairIso U V) :
    BananaMatrixAutGroup (perfectBanana (l + r)) :=
  classAction_descend bananaActualSubpairClass
    (fun {_ _} q => q.same_presented_class)
    (fun c U V q => Θ c (U := U) (V := V) q) p

/-- The descended action fixes identity arrows: the target-class proof
may differ from reflexivity, but all such proofs are proposition-irrelevant. -/
theorem bananaActualClassAction_descend_refl
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (Θ : ∀ (c : BananaPresentedIsoClass A)
        ⦃U V : BananaActualClassObject A c⦄,
      BananaActualSubpairIso U.1 V.1 →
        BananaMatrixAutGroup (perfectBanana (l + r)))
    (hId : ∀ (c : BananaPresentedIsoClass A)
          (U : BananaActualClassObject A c),
      Θ c (BananaActualSubpairIso.refl U.1) = 1)
    (U : BananaActualSubpair A) :
    bananaActualClassAction_descend Θ (BananaActualSubpairIso.refl U) = 1 := by
  exact classAction_descend_refl bananaActualSubpairClass
    (fun {_ _} p => p.same_presented_class)
    (fun c U V p => Θ c (U := U) (V := V) p)
    (fun U => BananaActualSubpairIso.refl U)
    (fun c U => hId c U) U

/-- A descended action preserves composition on ACTUAL partial
isomorphisms, including the change in the chosen source class index. -/
theorem bananaActualClassAction_descend_trans
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (Θ : ∀ (c : BananaPresentedIsoClass A)
        ⦃U V : BananaActualClassObject A c⦄,
      BananaActualSubpairIso U.1 V.1 →
        BananaMatrixAutGroup (perfectBanana (l + r)))
    (hComp : ∀ (c : BananaPresentedIsoClass A)
        (U V W : BananaActualClassObject A c)
        (p : BananaActualSubpairIso U.1 V.1)
        (q : BananaActualSubpairIso V.1 W.1),
      Θ c q * Θ c p = Θ c (p.trans q))
    {U V W : BananaActualSubpair A}
    (p : BananaActualSubpairIso U V)
    (q : BananaActualSubpairIso V W) :
    bananaActualClassAction_descend Θ q *
        bananaActualClassAction_descend Θ p =
      bananaActualClassAction_descend Θ (p.trans q) := by
  exact classAction_descend_trans bananaActualSubpairClass
    (fun {_ _} p => p.same_presented_class)
    (fun c U V p => Θ c (U := U) (V := V) p)
    (fun {_ _ _} p q => p.trans q)
    (fun c U V W p q => hComp c U V W p q) p q

/-- Inverses of actual partial isomorphisms descend to inverses of the
same ambient group element. -/
theorem bananaActualClassAction_descend_symm
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (Θ : ∀ (c : BananaPresentedIsoClass A)
        ⦃U V : BananaActualClassObject A c⦄,
      BananaActualSubpairIso U.1 V.1 →
        BananaMatrixAutGroup (perfectBanana (l + r)))
    (hInv : ∀ (c : BananaPresentedIsoClass A)
        (U V : BananaActualClassObject A c)
        (p : BananaActualSubpairIso U.1 V.1),
      (Θ c p)⁻¹ = Θ c p.symm)
    {U V : BananaActualSubpair A}
    (p : BananaActualSubpairIso U V) :
    (bananaActualClassAction_descend Θ p)⁻¹ =
      bananaActualClassAction_descend Θ p.symm := by
  exact classAction_descend_symm bananaActualSubpairClass
    (fun {_ _} p => p.same_presented_class)
    (fun c U V p => Θ c (U := U) (V := V) p)
    (fun {_ _} p => p.symm)
    (fun c U V p => hInv c U V p) p

/-- End-to-end coherent EPPA for an arbitrary finite BANANA pairing:
there exists a SINGLE automorphism of the perfect completion for each
actual two-sorted partial isomorphism, with coherent identity,
composition and inverse laws and the correct action on every actual
left- and right-sort element. The perfect-completion side dimension
is exactly l+r, including degenerate and one-sided cases. -/
theorem exists_bananaActualCoherentEPPA
    {l r : ℕ} (A : BananaMatrixStructure l r) :
    ∃ Θ : ∀ ⦃U V : BananaActualSubpair A⦄,
      BananaActualSubpairIso U V →
        BananaMatrixAutGroup (perfectBanana (l + r)),
      (∀ U : BananaActualSubpair A,
        Θ (BananaActualSubpairIso.refl U) = 1) ∧
      (∀ (U V W : BananaActualSubpair A)
          (p : BananaActualSubpairIso U V)
          (q : BananaActualSubpairIso V W),
        Θ q * Θ p = Θ (p.trans q)) ∧
      (∀ (U V : BananaActualSubpair A)
          (p : BananaActualSubpairIso U V),
        (Θ p)⁻¹ = Θ p.symm) ∧
      (∀ (U V : BananaActualSubpair A)
          (p : BananaActualSubpairIso U V),
        (∀ x : U.left,
          (Θ p).1.1 (A.completionEmbedding.left x.val) =
            A.completionEmbedding.left (p.left x).val) ∧
        (∀ y : U.right,
          (Θ p).1.2 (A.completionEmbedding.right y.val) =
            A.completionEmbedding.right (p.right y).val)) := by
  classical
  obtain ⟨Φ, hId, hComp, hInv, hExt⟩ :=
    exists_bananaActualClassCoherentExtension A
  let Θ : ∀ ⦃U V : BananaActualSubpair A⦄,
      BananaActualSubpairIso U V →
        BananaMatrixAutGroup (perfectBanana (l + r)) :=
    fun {_ _} p => bananaActualClassAction_descend Φ p
  refine ⟨Θ, ?_, ?_, ?_, ?_⟩
  · intro U
    exact bananaActualClassAction_descend_refl Φ hId U
  · intro U V W p q
    exact bananaActualClassAction_descend_trans Φ hComp p q
  · intro U V p
    exact bananaActualClassAction_descend_symm Φ hInv p
  · intro U V p
    exact hExt (bananaActualSubpairClass U)
      ⟨U, rfl⟩ ⟨V, p.same_presented_class.symm⟩ p

end SuccessorTree.NonPrecompact
