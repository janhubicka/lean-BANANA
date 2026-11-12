import BANANA.NonPrecompact.BananaMatrixCoherentClassFamily
import BANANA.NonPrecompact.Completion
import BANANA.NonPrecompact.BananaFiniteFraisseProperties

/-!
# An isomorphism-class atlas of embedded finite BANANA subpairs

A *presented subpair* comprises finite coordinate vector spaces, their
induced pairing, and a genuine embedding into a fixed finite BANANA
structure. The dimension bound follows from injectivity via finrank.
The existing hereditary theorem supplies a presentation for every pair
of actual vector subspaces, without any additional hypotheses.

The isomorphism relation on presentations is an equivalence relation.
Its quotient supplies one representative for each class and an
isomorphism from it to every presentation of that class.

This theorem is about the entire type of coordinate presentations.
Every pair of actual subspaces has a presentation by the existing
hereditary theorem. The remaining bridge selects one presentation per
actual subpair and transports actual partial isomorphisms to the atlas.
-/

namespace SuccessorTree.NonPrecompact

/-- A two-sorted finite subpair presented in coordinates, together with
its embedding into the fixed original finite BANANA structure. -/
structure BananaPresentedSubpair {l r : ℕ}
    (A : BananaMatrixStructure l r) where
  leftDim : ℕ
  rightDim : ℕ
  carrier : BananaMatrixStructure leftDim rightDim
  inclusion : BananaMatrixEmbedding carrier A

/-- An injective two-sorted linear embedding cannot increase the
dimension on either side, including when one side is zero. -/
theorem BananaMatrixEmbedding.coordinateDim_le
    {l r a b : ℕ} {A : BananaMatrixStructure l r}
    {B : BananaMatrixStructure a b} (e : BananaMatrixEmbedding B A) :
    a ≤ l ∧ b ≤ r := by
  classical
  have hL : finrank F2 (Fin a → F2) ≤ finrank F2 (Fin l → F2) :=
    (LinearEquiv.ofInjective e.left e.left_injective).finrank_eq.le.trans
      (LinearMap.range e.left).finrank_le
  have hR : finrank F2 (Fin b → F2) ≤ finrank F2 (Fin r → F2) :=
    (LinearEquiv.ofInjective e.right e.right_injective).finrank_eq.le.trans
      (LinearMap.range e.right).finrank_le
  constructor
  · simpa [Module.finrank_fintype_fun_eq_card] using hL
  · simpa [Module.finrank_fintype_fun_eq_card] using hR

/-- Every presented subpair satisfies the common-witness dimension bound. -/
theorem BananaPresentedSubpair.dimension_bound
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U : BananaPresentedSubpair A) : U.leftDim + U.rightDim ≤ l + r := by
  obtain ⟨hL, hR⟩ := U.inclusion.coordinateDim_le
  omega

/-- The existing hereditary theorem supplies coordinates for any actual
pair of left/right subspaces, with exact image ranges. -/
theorem BananaMatrixStructure.exists_presentedSubpair_with_ranges
    {l r : ℕ} (A : BananaMatrixStructure l r)
    (U : Submodule F2 (Fin l → F2))
    (V : Submodule F2 (Fin r → F2)) :
    ∃ P : BananaPresentedSubpair A,
      LinearMap.range P.inclusion.left = U ∧
      LinearMap.range P.inclusion.right = V := by
  obtain ⟨a, b, B, e, hL, hR⟩ := A.exists_substructure_with_ranges U V
  exact ⟨⟨a, b, B, e⟩, hL, hR⟩

/-- Isomorphism of presented subpairs ignores the embedding into the
ambient structure but preserves the abstract bilinear pairing. -/
def bananaPresentedIsoSetoid {l r : ℕ} (A : BananaMatrixStructure l r) :
    Setoid (BananaPresentedSubpair A) where
  r U V := Nonempty (BananaMatrixIso U.carrier V.carrier)
  iseqv := by
    constructor
    · intro U
      exact ⟨BananaMatrixIso.refl U.carrier⟩
    · intro U V h
      obtain ⟨p⟩ := h
      exact ⟨p.symm⟩
    · intro U V W hUV hVW
      obtain ⟨p⟩ := hUV
      obtain ⟨q⟩ := hVW
      exact ⟨p.trans q⟩

/-- Quotient by actual pairing-preserving two-sorted isomorphism. -/
abbrev BananaPresentedIsoClass {l r : ℕ}
    (A : BananaMatrixStructure l r) :=
  Quotient (bananaPresentedIsoSetoid A)

def bananaPresentedClassOf {l r : ℕ} {A : BananaMatrixStructure l r}
    (U : BananaPresentedSubpair A) : BananaPresentedIsoClass A :=
  Quotient.mk (bananaPresentedIsoSetoid A) U

/-- A representative is chosen exactly once per quotient class. -/
noncomputable def bananaPresentedRepresentative
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (c : BananaPresentedIsoClass A) : BananaPresentedSubpair A :=
  Quotient.out c

theorem bananaPresentedRepresentative_class
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (c : BananaPresentedIsoClass A) :
    bananaPresentedClassOf (bananaPresentedRepresentative c) = c :=
  Quotient.out_eq c

theorem bananaPresentedClassOf_eq_of_iso
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U V : BananaPresentedSubpair A)
    (p : BananaMatrixIso U.carrier V.carrier) :
    bananaPresentedClassOf U = bananaPresentedClassOf V :=
  Quotient.sound ⟨p⟩

/-- Presentations belonging to one specified isomorphism class. -/
abbrev BananaPresentedClassObject
    {l r : ℕ} (A : BananaMatrixStructure l r)
    (c : BananaPresentedIsoClass A) :=
  {U : BananaPresentedSubpair A // bananaPresentedClassOf U = c}

/-- Equality of quotient classes gives an actual pairing-preserving
isomorphism between the selected representative and each class member. -/
noncomputable def bananaPresentedRepresentativeIso
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (c : BananaPresentedIsoClass A)
    (U : BananaPresentedClassObject A c) :
    BananaMatrixIso (bananaPresentedRepresentative c).carrier U.1.carrier := by
  classical
  have hClass :
      bananaPresentedClassOf (bananaPresentedRepresentative c) =
        bananaPresentedClassOf U.1 := by
    exact (bananaPresentedRepresentative_class c).trans U.2.symm
  have hRel : (bananaPresentedIsoSetoid A).r
      (bananaPresentedRepresentative c) U.1 := Quotient.exact hClass
  exact Classical.choice hRel

/-- The original completion embedding takes every presented subpair into
the SAME standard perfect witness of side dimension l+r. -/
def BananaPresentedSubpair.toPerfectCompletion
    {l r : ℕ} {A : BananaMatrixStructure l r}
    (U : BananaPresentedSubpair A) :
    BananaMatrixEmbedding U.carrier (perfectBanana (l + r)) :=
  BananaMatrixEmbedding.comp A.completionEmbedding U.inclusion

/-- Choose class representatives and coherent extension assignments for
ALL finite embedded coordinate presentations at once. No individual
representative or dimension hypotheses are supplied by the caller.

The final passage from presentations to actual subspaces and their
partial automorphisms remains a separate groupoid-law obligation. -/
theorem exists_bananaPresentedClassCoherentExtension
    {l r : ℕ} (A : BananaMatrixStructure l r) :
    ∃ Θ : ∀ (c : BananaPresentedIsoClass A)
        ⦃U V : BananaPresentedClassObject A c⦄,
      BananaMatrixIso U.1.carrier V.1.carrier →
        BananaMatrixAutGroup (perfectBanana (l + r)),
      (∀ (c : BananaPresentedIsoClass A)
          (U : BananaPresentedClassObject A c),
        Θ c (BananaMatrixIso.refl U.1.carrier) = 1) ∧
      (∀ (c : BananaPresentedIsoClass A)
          (U V W : BananaPresentedClassObject A c)
          (p : BananaMatrixIso U.1.carrier V.1.carrier)
          (q : BananaMatrixIso V.1.carrier W.1.carrier),
        Θ c q * Θ c p = Θ c (p.trans q)) ∧
      (∀ (c : BananaPresentedIsoClass A)
          (U V : BananaPresentedClassObject A c)
          (p : BananaMatrixIso U.1.carrier V.1.carrier),
        (Θ c p)⁻¹ = Θ c p.symm) ∧
      (∀ (c : BananaPresentedIsoClass A)
          (U V : BananaPresentedClassObject A c)
          (p : BananaMatrixIso U.1.carrier V.1.carrier),
        (∀ x, (Θ c p).1.1 (U.1.toPerfectCompletion.left x) =
          V.1.toPerfectCompletion.left (p.left x)) ∧
        (∀ y, (Θ c p).1.2 (U.1.toPerfectCompletion.right y) =
          V.1.toPerfectCompletion.right (p.right y))) := by
  classical
  let I := BananaPresentedIsoClass A
  let O : I → Type := BananaPresentedClassObject A
  let aL : I → ℕ := fun c => (bananaPresentedRepresentative c).leftDim
  let aR : I → ℕ := fun c => (bananaPresentedRepresentative c).rightDim
  let dL : ∀ c : I, O c → ℕ := fun _ U => U.1.leftDim
  let dR : ∀ c : I, O c → ℕ := fun _ U => U.1.rightDim
  let A₀ : ∀ c : I, BananaMatrixStructure (aL c) (aR c) :=
    fun c => (bananaPresentedRepresentative c).carrier
  let B : ∀ c : I, ∀ U : O c, BananaMatrixStructure (dL c U) (dR c U) :=
    fun _ U => U.1.carrier
  have hDim : ∀ c : I, aL c + aR c ≤ l + r :=
    fun c => (bananaPresentedRepresentative c).dimension_bound
  let j₀ : ∀ c : I, BananaMatrixEmbedding (A₀ c) (perfectBanana (l + r)) :=
    fun c => (bananaPresentedRepresentative c).toPerfectCompletion
  let i : ∀ c : I, ∀ U : O c, BananaMatrixIso (A₀ c) (B c U) :=
    fun c U => bananaPresentedRepresentativeIso c U
  let j : ∀ c : I, ∀ U : O c,
      BananaMatrixEmbedding (B c U) (perfectBanana (l + r)) :=
    fun _ U => U.1.toPerfectCompletion
  exact exists_bananaMatrixCoherentClassFamily
    O aL aR dL dR A₀ B hDim j₀ i j

end SuccessorTree.NonPrecompact
