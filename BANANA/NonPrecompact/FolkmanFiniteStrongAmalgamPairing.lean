import BANANA.NonPrecompact.FolkmanActualTwoSortPairingBilinear

/-!
# Complete finite-atom Folkman--BANANA strong amalgamation certificate

This result combines the explicit pairing extension on the actual
atom-grid-plus-private-point rings with the already checked *two-sort*
Boolean-ring strong-intersection theorem.

The sources are arbitrary finite atom presentations, including empty
atom sets (zero rings), and the embeddings are non-unital.

Remaining global interface: show that an arbitrary diagram of finite
Boolean rings with a bilinear pairing is isomorphic to one of these
finite atom presentations. Once that is supplied, this certificate
yields the class-level strong amalgamation used in the circulation paper.
-/

namespace SuccessorTree.NonPrecompact
open scoped Classical

namespace FolkmanFiniteTwoSortAtomDiagram

variable {AL BL CL AR BR CR : Type*}
variable [Fintype AL] [Fintype BL] [Fintype CL]
variable [Fintype AR] [Fintype BR] [Fintype CR]

/-- The actual finite ring-pair amalgam admits a bilinear pairing
extending both input pairings. The two source images intersect in
exactly their common base, and that base is shared in both sorts. -/
theorem exists_strong_amalgam_pairing
    (D : FolkmanFiniteTwoSortAtomDiagram AL BL CL AR BR CR)
    (βA : Finset AL → Finset AR → F2)
    (βB : Finset BL → Finset BR → F2)
    (βC : Finset CL → Finset CR → F2)
    (hAleft : ∀ a a' r,
      βA (symmDiff a a') r = βA a r + βA a' r)
    (hBleft : ∀ b b' r,
      βB (symmDiff b b') r = βB b r + βB b' r)
    (hCleft : ∀ c c' r,
      βC (symmDiff c c') r = βC c r + βC c' r)
    (hAright : ∀ a r r',
      βA a (symmDiff r r') = βA a r + βA a r')
    (hBright : ∀ b r r',
      βB b (symmDiff r r') = βB b r + βB b r')
    (hCright : ∀ c r r',
      βC c (symmDiff r r') = βC c r + βC c r')
    (hcommonB : ∀ a r,
      βB (folkmanFinsetBaseLeft D.fL a)
        (folkmanFinsetBaseLeft D.fR r) = βA a r)
    (hcommonC : ∀ a r,
      βC (folkmanFinsetBaseRight D.gL a)
        (folkmanFinsetBaseRight D.gR r) = βA a r) :
    ∃ βD :
      Finset (FolkmanAtomAmalgam D.fL D.gL) →
      Finset (FolkmanAtomAmalgam D.fR D.gR) → F2,
      (∀ x x' y, βD (symmDiff x x') y =
        βD x y + βD x' y) ∧
      (∀ x y y', βD x (symmDiff y y') =
        βD x y + βD x y') ∧
      (∀ x y, βD (D.embedB (x,y)).1
        (D.embedB (x,y)).2 = βB x y) ∧
      (∀ x y, βD (D.embedC (x,y)).1
        (D.embedC (x,y)).2 = βC x y) ∧
      (∀ b : Finset BL × Finset BR,
        ∀ c : Finset CL × Finset CR,
          D.embedB b = D.embedC c ↔
          ∃ a : Finset AL × Finset AR,
            b = D.baseB a ∧ c = D.baseC a) := by
  obtain ⟨βD, hleft, hright, hB, hC⟩ :=
    D.exists_actual_compatible_pairing βA βB βC
      hAleft hBleft hCleft hAright hBright hCright
      hcommonB hcommonC
  refine ⟨βD, hleft, hright, hB, hC, ?_⟩
  intro b c
  exact D.images_eq_iff_common_base b c

end FolkmanFiniteTwoSortAtomDiagram
end SuccessorTree.NonPrecompact
