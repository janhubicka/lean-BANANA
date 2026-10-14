import BANANA.NonPrecompact.PrebananaAmenabilityMeasureObstruction

/-!
# The unmarked three-atom copy supplies both mass partitions

The algebraic non-amenability argument previously assumed partitions
of the unit into two and three proper nonzero zero-marked elements.

Here one **marked embedding** of the unmarked three-atom Boolean
algebra supplies both partitions. The source is represented by
`Finset (Fin 3)` and an injective bounded-lattice homomorphism into
an arbitrary (possibly infinite) Boolean algebra.

Together with a group orbit-transitivity assumption and finite
additivity of an invariant mass, this yields a contradiction.
No construction of the countable Fraïssé limit or Stone space is
claimed; those remain separate, standard external interfaces.
-/

namespace SuccessorTree.NonPrecompact

/-- A marked, injective embedding of the unmarked three-atom
powerset supplies the two and three partitions required to
rule out one common finitely additive mass on the proper
nonzero zero-marked elements of the target. -/
theorem prebanana_no_uniformMass_of_threeAtom_copy
    {β : Type*} [BooleanAlgebra β]
    (μ : β → F2) (mass : β → ℝ)
    (hadd : ∀ x y : β, x ⊓ y = ⊥ →
      mass (x ⊔ y) = mass x + mass y)
    (hunit : mass ⊤ = 1)
    (hequal : ∀ x y : β,
      prebananaProperZeroMark μ x →
      prebananaProperZeroMark μ y →
      mass x = mass y)
    (f : BoundedLatticeHom (Finset (Fin 3)) β)
    (hinj : Function.Injective f)
    (hmark : ∀ s : Finset (Fin 3), μ (f s) = 0) :
    False := by
  let a : Finset (Fin 3) := {0}
  let b : Finset (Fin 3) := {1, 2}
  let d : Finset (Fin 3) := {1}
  let e : Finset (Fin 3) := {2}
  have hproper (s : Finset (Fin 3))
      (hbot : s ≠ ∅) (htop : s ≠ Finset.univ) :
      prebananaProperZeroMark μ (f s) := by
    refine ⟨?_, ?_, hmark s⟩
    · intro h
      apply hbot
      apply hinj
      calc
        f s = ⊥ := h
        _ = f (⊥ : Finset (Fin 3)) := (map_bot f).symm
    · intro h
      apply htop
      apply hinj
      calc
        f s = ⊤ := h
        _ = f (⊤ : Finset (Fin 3)) := (map_top f).symm
  have hdj (s t : Finset (Fin 3))
      (h : s ∩ t = ∅) : f s ⊓ f t = ⊥ := by
    have h' : s ⊓ t = (⊥ : Finset (Fin 3)) := by simpa using h
    calc
      f s ⊓ f t = f (s ⊓ t) := (map_inf f s t).symm
      _ = f ⊥ := congrArg f h'
      _ = ⊥ := map_bot f
  have hjoin (s t : Finset (Fin 3))
      (h : s ∪ t = Finset.univ) : f s ⊔ f t = ⊤ := by
    have h' : s ⊔ t = (⊤ : Finset (Fin 3)) := by simpa using h
    calc
      f s ⊔ f t = f (s ⊔ t) := (map_sup f s t).symm
      _ = f ⊤ := congrArg f h'
      _ = ⊤ := map_top f
  have ha0 : a ≠ ∅ := by decide
  have ha1 : a ≠ Finset.univ := by decide
  have hb0 : b ≠ ∅ := by decide
  have hb1 : b ≠ Finset.univ := by decide
  have hd0 : d ≠ ∅ := by decide
  have hd1 : d ≠ Finset.univ := by decide
  have he0 : e ≠ ∅ := by decide
  have he1 : e ≠ Finset.univ := by decide
  have hpair :
      a ∩ b = ∅ ∧ a ∪ b = Finset.univ := by
    simpa [a, b] using prebanana_threeAtom_unmarked_pair
  have htriple :
      a ∩ d = ∅ ∧ a ∩ e = ∅ ∧ d ∩ e = ∅ ∧
        (a ∪ d) ∪ e = Finset.univ := by
    simpa [a, d, e] using prebanana_threeAtom_unmarked_triple
  rcases hpair with ⟨hpairdj, hpairtop⟩
  rcases htriple with ⟨had, hae, hde, htrtop⟩
  have htripleTop : (f a ⊔ f d) ⊔ f e = ⊤ := by
    have htr' : (a ⊔ d) ⊔ e = (⊤ : Finset (Fin 3)) := by
      simpa using htrtop
    calc
      (f a ⊔ f d) ⊔ f e = f (a ⊔ d) ⊔ f e := by
        rw [map_sup f a d]
      _ = f ((a ⊔ d) ⊔ e) :=
        (map_sup f (a ⊔ d) e).symm
      _ = f ⊤ := congrArg f htr'
      _ = ⊤ := map_top f
  exact prebanana_no_uniformMass_two_three μ mass hadd hunit hequal
    (f a) (f b) (f a) (f d) (f e)
    (hproper a ha0 ha1) (hproper b hb0 hb1)
    (hproper a ha0 ha1) (hproper d hd0 hd1)
    (hproper e he0 he1)
    (hdj a b hpairdj) (hjoin a b hpairtop)
    (hdj a d had) (hdj a e hae) (hdj d e hde)
    htripleTop

/-- A group-invariant mass is impossible once the target contains
one unmarked three-atom copy and the group is transitive on the
proper nonzero zero-marked elements. -/
theorem prebanana_no_invariantMass_of_threeAtom_copy
    {β G : Type*}
    [BooleanAlgebra β] [Group G] [MulAction G β]
    (μ : β → F2) (mass : β → ℝ)
    (hadd : ∀ x y : β, x ⊓ y = ⊥ →
      mass (x ⊔ y) = mass x + mass y)
    (hunit : mass ⊤ = 1)
    (htrans : ∀ x y : β,
      prebananaProperZeroMark μ x →
      prebananaProperZeroMark μ y →
      ∃ g : G, g • x = y)
    (hinv : ∀ g : G, ∀ x : β, mass (g • x) = mass x)
    (f : BoundedLatticeHom (Finset (Fin 3)) β)
    (hinj : Function.Injective f)
    (hmark : ∀ s : Finset (Fin 3), μ (f s) = 0) :
    False :=
  prebanana_no_uniformMass_of_threeAtom_copy μ mass hadd hunit
    (prebanana_invariantMass_constant_on_zeroMark_orbit
      μ mass htrans hinv)
    f hinj hmark

end SuccessorTree.NonPrecompact
