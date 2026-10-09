import BANANA.NonPrecompact.BananaTripleStrongImages

/-!
# Exact intersection of the triple-coordinate images

Given linear embeddings f : A → B and g : A → C and linear left
inverses p, q, the two redundant-coordinate maps
  b ↦ (p b, b - f(p b), 0)
  c ↦ (q c, 0, c - g(q c))
agree on A and intersect exactly there. No pairing assumptions are
needed: the result is a purely linear statement valid over F₂.
-/

namespace SuccessorTree.NonPrecompact

/-- The maps agree on the common source, provided the selected
projections are retractions of the two embeddings. -/
theorem tripleInl_comp_eq_tripleInr_comp
    {a b c : ℕ}
    (f : (Fin a → F2) →ₗ[F2] (Fin b → F2))
    (g : (Fin a → F2) →ₗ[F2] (Fin c → F2))
    (p : (Fin b → F2) →ₗ[F2] (Fin a → F2))
    (q : (Fin c → F2) →ₗ[F2] (Fin a → F2))
    (hpf : ∀ z, p (f z) = z)
    (hqg : ∀ z, q (g z) = z)
    (z : Fin a → F2) :
    tripleInl (c := c) f p (f z) =
      tripleInr (b := b) g q (g z) := by
  change
    Fin.append
      (Fin.append (p (f z)) (f z - f (p (f z)))) 0 =
    Fin.append
      (Fin.append (q (g z)) 0) (g z - g (q (g z)))
  simp [hpf z, hqg z]

/-- Strong intersection of the two images: equality in the
redundant triple space holds exactly for points in the common
source. No injectivity hypothesis is needed separately, since
the retraction equations imply it. -/
theorem tripleInl_eq_tripleInr_iff_common
    {a b c : ℕ}
    (f : (Fin a → F2) →ₗ[F2] (Fin b → F2))
    (g : (Fin a → F2) →ₗ[F2] (Fin c → F2))
    (p : (Fin b → F2) →ₗ[F2] (Fin a → F2))
    (q : (Fin c → F2) →ₗ[F2] (Fin a → F2))
    (hpf : ∀ z, p (f z) = z)
    (hqg : ∀ z, q (g z) = z)
    (x : Fin b → F2) (y : Fin c → F2) :
    tripleInl (c := c) f p x =
        tripleInr (b := b) g q y ↔
      ∃ z : Fin a → F2, x = f z ∧ y = g z := by
  constructor
  · intro h
    have hA : p x = q y := by
      have hh := congrArg (tripleProjA (a := a) (b := b) (c := c)) h
      simpa only [tripleProjA_inl, tripleProjA_inr] using hh
    have hB : x - f (p x) = 0 := by
      have hh := congrArg (tripleProjB (a := a) (b := b) (c := c)) h
      simpa only [tripleProjB_inl, tripleProjB_inr] using hh
    have hC : 0 = y - g (q y) := by
      have hh := congrArg (tripleProjC (a := a) (b := b) (c := c)) h
      simpa only [tripleProjC_inl, tripleProjC_inr] using hh
    have hx : x = f (p x) := sub_eq_zero.mp hB
    have hy : y = g (q y) := sub_eq_zero.mp hC.symm
    refine ⟨p x, hx, ?_⟩
    calc
      y = g (q y) := hy
      _ = g (p x) := by rw [hA]
  · rintro ⟨z, rfl, rfl⟩
    exact tripleInl_comp_eq_tripleInr_comp f g p q hpf hqg z

end SuccessorTree.NonPrecompact
