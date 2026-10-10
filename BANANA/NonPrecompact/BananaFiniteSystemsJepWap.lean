import BANANA.NonPrecompact.BananaStandardPerfectSystems
import BANANA.NonPrecompact.BananaPerfectTotalDiagramAmalgam
import BANANA.NonPrecompact.BananaFiniteSystemCofinalTransfer

/-!
# JEP and WAP for all finite BANANA n-systems

The class of standard perfect-total systems is cofinal among finite
systems of partial automorphisms. The algebraic perfect-diagram
amalgamation theorem provides AP in this cofinal subclass.

The zero-dimensional perfect system embeds into every standard
perfect system, giving JEP within the cofinal subclass.

Applying the independently formalised categorical transfer gives
JEP and WAP for *all* finite BANANA n-systems. This is the
finite-combinatorial hypothesis of the Kechris--Rosendal criterion
for ample generics. Applying that general topological criterion is
a separate standard theorem and is not claimed here.
-/

namespace SuccessorTree.NonPrecompact

namespace BananaStandardPerfectSystem

variable {n : ℕ}

/-- Amalgamation of arbitrary standard perfect-total systems.
The resulting genuine system embeddings agree on the common
system on both sorts. -/
theorem exists_amalgam
    (A B C : BananaStandardPerfectSystem n)
    (f : Embedding A B)
    (g : Embedding A C) :
    ∃ D : BananaStandardPerfectSystem n,
    ∃ h : Embedding B D,
    ∃ k : Embedding C D,
      bananaSystemEmbeddingsAgree
        (h.toPartial.comp f.toPartial)
        (k.toPartial.comp g.toPartial) := by
  obtain ⟨d, eB, eC, FD, hAL, hAR, hBL, hBR, hCL, hCR⟩ :=
    exists_bananaPerfectTotalSystem_perfect_amalgam
      f.carrier g.carrier A.actions B.actions C.actions
      f.intertwines_left f.intertwines_right
      g.intertwines_left g.intertwines_right
  let D : BananaStandardPerfectSystem n :=
    { dimension := d, actions := FD }
  let h : Embedding B D :=
    { carrier := eB
      intertwines_left := hBL
      intertwines_right := hBR }
  let k : Embedding C D :=
    { carrier := eC
      intertwines_left := hCL
      intertwines_right := hCR }
  refine ⟨D, h, k, ?_⟩
  constructor
  · intro x
    change eB.left (f.carrier.left x) =
      eC.left (g.carrier.left x)
    exact hAL x
  · intro y
    change eB.right (f.carrier.right y) =
      eC.right (g.carrier.right y)
    exact hAR y

/-- The zero-dimensional standard perfect n-system, with all named
automorphisms equal to the identity. -/
def zero (n : ℕ) : BananaStandardPerfectSystem n :=
  { dimension := 0
    actions := fun _ => BananaMatrixEmbedding.id (perfectBanana 0) }

/-- The zero-dimensional system embeds into every standard perfect
system, on both sorts and for every named automorphism. -/
def zeroEmbedding (S : BananaStandardPerfectSystem n) :
    Embedding (zero n) S := by
  haveI : Subsingleton (Fin (zero n).dimension → F2) := by
    constructor
    intro x y
    funext i
    exact Fin.elim0 i
  refine {
    carrier := {
      left := 0
      right := 0
      left_injective := by
        intro x y _
        exact Subsingleton.elim x y
      right_injective := by
        intro x y _
        exact Subsingleton.elim x y
      pairing_apply := by
        intro x y
        have hx : x = 0 := Subsingleton.elim x 0
        have hy : y = 0 := Subsingleton.elim y 0
        subst x
        subst y
        simp [perfectBanana_eval]
    }
    intertwines_left := by
      intro i x
      have hx : x = 0 := Subsingleton.elim x 0
      subst x
      simp
    intertwines_right := by
      intro i y
      have hy : y = 0 := Subsingleton.elim y 0
      subst y
      simp
  }

/-- Any two standard perfect-total n-systems jointly embed into
another standard perfect-total system. -/
theorem exists_joint_embedding
    (S T : BananaStandardPerfectSystem n) :
    ∃ U : BananaStandardPerfectSystem n,
      Nonempty (Embedding S U) ∧ Nonempty (Embedding T U) := by
  obtain ⟨U, h, k, _⟩ :=
    exists_amalgam (zero n) S T (zeroEmbedding S) (zeroEmbedding T)
  exact ⟨U, ⟨h⟩, ⟨k⟩⟩

end BananaStandardPerfectSystem

/-- The precise cofinal subclass of ordinary finite n-systems:
systems literally presented by one standard perfect pairing and
n total self-automorphisms. -/
def bananaStandardPerfectGood {n : ℕ}
    (S : BananaFinitePartialSystem n) : Prop :=
  ∃ P : BananaStandardPerfectSystem n, S = P.toPartial

/-- Every finite system embeds into a member of the chosen subclass. -/
theorem bananaStandardPerfectGood_cofinal (n : ℕ) :
    BananaFiniteSystemsCofinal
      (bananaStandardPerfectGood (n := n)) := by
  intro S
  obtain ⟨P, ⟨e⟩⟩ := exists_bananaStandardPerfectSystem_extension S
  exact ⟨P.toPartial, ⟨P, rfl⟩, ⟨e⟩⟩

/-- The cofinal subclass has the joint embedding property. -/
theorem bananaStandardPerfectGood_jep (n : ℕ) :
    BananaFiniteGoodSystemsJEP
      (bananaStandardPerfectGood (n := n)) := by
  intro S T hS hT
  rcases hS with ⟨PS, rfl⟩
  rcases hT with ⟨PT, rfl⟩
  obtain ⟨U, ⟨f⟩, ⟨g⟩⟩ :=
    BananaStandardPerfectSystem.exists_joint_embedding PS PT
  exact ⟨U.toPartial, ⟨U, rfl⟩, ⟨f.toPartial⟩, ⟨g.toPartial⟩⟩

/-- The cofinal subclass has full amalgamation, with agreement on
the common system rather than only on its underlying pairing. -/
theorem bananaStandardPerfectGood_ap (n : ℕ) :
    BananaFiniteGoodSystemsAP
      (bananaStandardPerfectGood (n := n)) := by
  intro S T U hS hT hU f g
  rcases hS with ⟨PS, rfl⟩
  rcases hT with ⟨PT, rfl⟩
  rcases hU with ⟨PU, rfl⟩
  obtain ⟨V, h, k, hagree⟩ :=
    BananaStandardPerfectSystem.exists_amalgam PS PT PU
      (BananaStandardPerfectSystem.Embedding.ofPartial f)
      (BananaStandardPerfectSystem.Embedding.ofPartial g)
  exact ⟨V.toPartial, ⟨V, rfl⟩, h.toPartial, k.toPartial, hagree⟩

/-- All finite BANANA n-systems satisfy JEP and WAP. The latter
includes compatible morphisms for each named partial isomorphism. -/
theorem bananaFiniteSystems_jep_and_wap (n : ℕ) :
    BananaFiniteSystemsJEP n ∧ BananaFiniteSystemsWAP n := by
  constructor
  · exact bananaFiniteSystems_jep_of_cofinal
      (bananaStandardPerfectGood (n := n))
      (bananaStandardPerfectGood_cofinal n)
      (bananaStandardPerfectGood_jep n)
  · exact bananaFiniteSystems_wap_of_cofinal_amalgamation
      (bananaStandardPerfectGood (n := n))
      (bananaStandardPerfectGood_cofinal n)
      (bananaStandardPerfectGood_ap n)

end SuccessorTree.NonPrecompact
