import BANANA.NonPrecompact.BananaFiniteSystemPerfectTotalCofinality

/-!
# The cofinal class of standard perfect-total BANANA systems

A standard perfect-total n-system is one standard perfect pairing
together with n named automorphisms. Its corresponding ordinary
n-system has full domain and the identity domain embedding for each
name; the range embedding is the selected automorphism.

Every finite system of partial automorphisms embeds into one of these
standard systems, using the already verified common perfect
completion. In this representation, system embeddings are exactly
pairing embeddings intertwining each named automorphism on both
sorts.

This prepares a direct proof of amalgamation in the cofinal subclass.
The abstract categorical AP/JEP/WAP deductions are separate.
-/

namespace SuccessorTree.NonPrecompact

/-- One standard perfect pairing equipped with n total
automorphisms of that pairing. -/
structure BananaStandardPerfectSystem (n : ℕ) where
  dimension : ℕ
  actions : Fin n →
    BananaMatrixEmbedding (perfectBanana dimension)
      (perfectBanana dimension)

namespace BananaStandardPerfectSystem

variable {n : ℕ}

/-- Regard the standard perfect-total system as an ordinary
finite system of partial automorphisms (all partial maps are total). -/
def toPartial (S : BananaStandardPerfectSystem n) :
    BananaFinitePartialSystem n where
  leftDim := S.dimension
  rightDim := S.dimension
  carrier := perfectBanana S.dimension
  sourceLeftDim := fun _ => S.dimension
  sourceRightDim := fun _ => S.dimension
  source := fun _ => perfectBanana S.dimension
  domain := fun _ => BananaMatrixEmbedding.id (perfectBanana S.dimension)
  range := S.actions

/-- A genuine embedding of standard perfect-total systems is a
pairing embedding intertwining all named automorphisms on both sorts. -/
structure Embedding (S T : BananaStandardPerfectSystem n) where
  carrier : BananaMatrixEmbedding
    (perfectBanana S.dimension) (perfectBanana T.dimension)
  intertwines_left : ∀ (i : Fin n) (x : Fin S.dimension → F2),
    (T.actions i).left (carrier.left x) =
      carrier.left ((S.actions i).left x)
  intertwines_right : ∀ (i : Fin n) (y : Fin S.dimension → F2),
    (T.actions i).right (carrier.right y) =
      carrier.right ((S.actions i).right y)

/-- Every intertwining pairing embedding is also an embedding of
the underlying labelled partial-automorphism systems. -/
def Embedding.toPartial {S T : BananaStandardPerfectSystem n}
    (f : Embedding S T) :
    BananaFinitePartialSystemEmbedding S.toPartial T.toPartial where
  carrier := f.carrier
  source := fun _ => f.carrier
  domain_left := by intro i x; rfl
  domain_right := by intro i y; rfl
  range_left := by
    intro i x
    exact (f.intertwines_left i x).symm
  range_right := by
    intro i y
    exact (f.intertwines_right i y).symm

/-- Conversely, the four commuting squares of a partial-system
embedding give precisely the two required intertwining identities. -/
def Embedding.ofPartial {S T : BananaStandardPerfectSystem n}
    (f : BananaFinitePartialSystemEmbedding S.toPartial T.toPartial) :
    Embedding S T where
  carrier := f.carrier
  intertwines_left := by
    intro i x
    have hd : f.carrier.left x = (f.source i).left x := by
      exact f.domain_left i x
    have hr :
        f.carrier.left ((S.actions i).left x) =
          (T.actions i).left ((f.source i).left x) := by
      exact f.range_left i x
    rw [hd]
    exact hr.symm
  intertwines_right := by
    intro i y
    have hd : f.carrier.right y = (f.source i).right y := by
      exact f.domain_right i y
    have hr :
        f.carrier.right ((S.actions i).right y) =
          (T.actions i).right ((f.source i).right y) := by
      exact f.range_right i y
    rw [hd]
    exact hr.symm

end BananaStandardPerfectSystem

/-- The standard perfect-total systems are cofinal among all finite
systems of n labelled partial automorphisms, with the extension
witnessed by a *genuine system embedding*. -/
theorem exists_bananaStandardPerfectSystem_extension
    {n : ℕ} (S : BananaFinitePartialSystem n) :
    ∃ P : BananaStandardPerfectSystem n,
      Nonempty (BananaFinitePartialSystemEmbedding S P.toPartial) := by
  let k := S.leftDim + S.rightDim
  obtain ⟨f, H, hL, hR⟩ :=
    exists_common_perfect_completion_total_family
      S.carrier S.sourceLeftDim S.sourceRightDim
      S.source S.domain S.range
  let P : BananaStandardPerfectSystem n :=
    { dimension := k, actions := H }
  refine ⟨P, ⟨{
    carrier := f
    source := fun i => BananaMatrixEmbedding.comp f (S.domain i)
    domain_left := by
      intro i x
      rfl
    domain_right := by
      intro i y
      rfl
    range_left := by
      intro i x
      exact (hL i x).symm
    range_right := by
      intro i y
      exact (hR i y).symm
  }⟩⟩

end SuccessorTree.NonPrecompact
