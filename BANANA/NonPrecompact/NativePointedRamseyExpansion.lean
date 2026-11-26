import BANANA.NonPrecompact.BananaNativeCopySystem
import BANANA.NonPrecompact.BooleanBananaCopyTransport
import BANANA.NonPrecompact.FolkmanRamseyExpansionObstruction

/-!
# Generated expansion bounds for native copy systems

An expanded object may contain strictly more points than the reduct copy
that generates it. A finite family of pointed expanded objects covering
the reduct copies suffices for the Ramsey-degree argument. No encoding
of the native sorts by a product or a disjoint union is required here.

The hypotheses express the reduct functor, the Ramsey property of the
expanded category, and the finite pointed cover. In a hereditary class
of finite expansions, a finite list of generated pointed expansion types
gives the cover by restricting to the generated substructures.
-/

namespace SuccessorTree

/-- Only the data of an expansion needed by the pointed Ramsey argument.
The reduct of an expanded object is a native object, and expanded
embeddings induce native embeddings respecting composition. -/
structure PointedRamseyExpansion (S : FiniteCopySystem) (T : FiniteCopySystem) where
  reduct : T.Obj → S.Obj
  mapEmb : ∀ {A B : T.Obj}, T.Emb A B → S.Emb (reduct A) (reduct B)
  mapEmb_comp : ∀ {A B C : T.Obj} (f : T.Emb A B) (g : T.Emb B C),
    mapEmb (T.compEmb f g) = S.compEmb (mapEmb f) (mapEmb g)
  liftObj : ∀ B : S.Obj, ∃ B' : T.Obj, Nonempty (S.Emb B (reduct B'))
  ramsey : ∀ (A B : T.Obj) (r : ℕ), 0 < r →
    ∃ C : T.Obj, ∀ colour : T.Emb A C → Fin r,
      ∃ g : T.Emb B C, ∀ e₁ e₂ : T.Emb A B,
        colour (T.compEmb e₁ g) = colour (T.compEmb e₂ g)

namespace PointedRamseyExpansion

variable {S : FiniteCopySystem} {T : FiniteCopySystem} (E : PointedRamseyExpansion S T)

/-- Every native copy in an expanded target is the image of one of a
uniformly bounded number of distinguished native copies in expanded
domains. These domains may have more points than the distinguished
copy. Representatives are allowed to depend on the expanded target. -/
def HasPointedCover (A : S.Obj) (t : ℕ) : Prop :=
  ∀ B : T.Obj, ∃ (D : Fin t → T.Obj)
    (p : ∀ i, S.Copy A (E.reduct (D i))),
      ∀ q : S.Copy A (E.reduct B),
        ∃ (i : Fin t) (e : T.Emb (D i) B), q = S.mapCopy (E.mapEmb e) (p i)

private theorem simultaneous (expansion : PointedRamseyExpansion S T) {I : Type*} (D : I → T.Obj)
    (types : Finset I) (B : T.Obj) (r : ℕ) (hr : 0 < r) :
    ∃ C : T.Obj, ∀ colour : ∀ i, T.Emb (D i) C → Fin r,
      ∃ g : T.Emb B C, ∀ i ∈ types, ∀ e₁ e₂ : T.Emb (D i) B,
        colour i (T.compEmb e₁ g) = colour i (T.compEmb e₂ g) := by
  classical
  induction types using Finset.induction_on with
  | empty =>
      exact ⟨B, fun _ => ⟨T.idEmb B, by simp⟩⟩
  | @insert i types _ ih =>
      obtain ⟨C₀, hC₀⟩ := ih
      obtain ⟨C, hC⟩ := expansion.ramsey (D i) C₀ r hr
      refine ⟨C, fun colour => ?_⟩
      obtain ⟨h, hh⟩ := hC (colour i)
      obtain ⟨g, hg⟩ := hC₀ (fun j e => colour j (T.compEmb e h))
      refine ⟨T.compEmb g h, fun j hj e₁ e₂ => ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [T.comp_assoc] using hh (T.compEmb e₁ g) (T.compEmb e₂ g)
      · simpa only [T.comp_assoc] using hg j hj e₁ e₂

/-- A finite cover by pointed generated expanded objects bounds the
native copy Ramsey degree. The proof does not require restriction of an
expanded structure to the carrier of the distinguished copy. -/
theorem copyRamseyDegreeLE_of_pointedCover (A : S.Obj) (t : ℕ)
    (hCover : E.HasPointedCover A t) : S.CopyRamseyDegreeLE A t := by
  classical
  intro B r hr
  obtain ⟨B', ⟨iB⟩⟩ := E.liftObj B
  obtain ⟨D, p, hB⟩ := hCover B'
  obtain ⟨C', hC'⟩ := simultaneous E D Finset.univ B' r hr
  refine ⟨E.reduct C', fun colouring => ?_⟩
  let colour (i : Fin t) (e : T.Emb (D i) C') : Fin r :=
    colouring (S.mapCopy (E.mapEmb e) (p i))
  obtain ⟨g, hg⟩ := hC' colour
  let f : S.Emb B (E.reduct C') := S.compEmb iB (E.mapEmb g)
  let colourByType (i : Fin t) : Fin r :=
    if h : Nonempty (T.Emb (D i) B') then
      colour i (T.compEmb (Classical.choice h) g)
    else ⟨0, hr⟩
  refine ⟨f, ?_⟩
  let _ := S.copyFintype A B
  have hsubset : S.coloursInside colouring f ⊆ Finset.univ.image colourByType := by
    intro c hc
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨i, e, he⟩ := hB (S.mapCopy iB q)
    have hmatch : S.mapCopy f q = S.mapCopy (E.mapEmb (T.compEmb e g)) (p i) := by
      change S.mapCopy (S.compEmb iB (E.mapEmb g)) q = _
      rw [S.mapCopy_comp, he, E.mapEmb_comp, S.mapCopy_comp]
    have h : Nonempty (T.Emb (D i) B') := ⟨e⟩
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    calc
      colourByType i = colour i (T.compEmb (Classical.choice h) g) := dite_eq_left h
      _ = colour i (T.compEmb e g) := hg i (Finset.mem_univ _) (Classical.choice h) e
      _ = colouring (S.mapCopy f q) := congrArg colouring hmatch.symm
  exact (Finset.card_le_card hsubset).trans (Finset.card_image_le.trans (by simp))

/-- A source with no finite copy Ramsey degree excludes any finite
pointed cover in such a Ramsey expansion. -/
theorem not_exists_pointedCover (A : S.Obj)
    (hInfinite : ∀ t : ℕ, ¬ S.CopyRamseyDegreeLE A t) :
    ¬ ∃ t : ℕ, E.HasPointedCover A t := by
  rintro ⟨t, ht⟩
  exact hInfinite t (E.copyRamseyDegreeLE_of_pointedCover A t ht)

end PointedRamseyExpansion

namespace NonPrecompact

/-- Native Boolean–BANANA obstruction for expansions allowing larger
generated substructures. -/
theorem booleanBanana_noFinitePointedCover {T : FiniteCopySystem}
    (E : PointedRamseyExpansion booleanBananaCopySystem T) :
    ¬ ∃ t : ℕ, E.HasPointedCover (booleanBananaAllMarkedPower 0) t :=
  E.not_exists_pointedCover _ booleanBananaTwoMarkedCopyRamseyDegree_infinite

/-- Native Folkman–BANANA obstruction, without a product encoding. -/
theorem folkmanNative_noFinitePointedCover {T : FiniteCopySystem}
    (E : PointedRamseyExpansion folkmanNativeCopySystem T) :
    ¬ ∃ t : ℕ, E.HasPointedCover (folkmanNativeDiagonal 1) t :=
  E.not_exists_pointedCover _ folkmanNativeCopyRamseyDegree_infinite

/-- Native BANANA obstruction, with copies given by the two image
subspaces of the native embeddings. -/
theorem banana_noFinitePointedCover {T : FiniteCopySystem}
    (E : PointedRamseyExpansion bananaCopySystem T) :
    ¬ ∃ t : ℕ, E.HasPointedCover ⟨1, 1, linePairSource 0⟩ t := by
  apply E.not_exists_pointedCover
  intro t h
  let A : BananaFiniteCopyObject := ⟨1, 1, linePairSource 0⟩
  exact A.matrix.copyRamseyDegree_infinite_of_positive (by decide) (by decide) t
    ((bananaCopySystem_copyRamseyDegreeLE_iff A t).mp h)

end NonPrecompact
end SuccessorTree
