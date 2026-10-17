import BANANA.NonPrecompact.PrebananaFiveAryCylinderFiniteAmbient
import BANANA.NonPrecompact.PrebananaFiveAryCylinderFiniteAge

/-!
# Finite marked presentations of tuples in the countable pre-BANANA model

Every finite tuple of the explicit countable cylinder algebra lies in
a finite Boolean subalgebra. The inherited marking makes that
subalgebra a finite pre-BANANA model and its inclusion into the
countable cylinder algebra is a genuine marked embedding.

This supplies the finite presentations needed to transfer the
already verified abstract finite marked-tuple profiles to the
countable model. There is no arbitrary atom enumeration in the
statement and no ultrahomogeneity assumption.
-/

namespace SuccessorTree.NonPrecompact

open scoped Classical

/-- Any finite tuple in the explicit countable marked cylinder
algebra admits one common *genuine marked finite model*
presentation, together with an embedding recovering every
coordinate of the tuple exactly. -/
theorem prebananaCylinder_exists_finiteTuplePresentation
    {k : ℕ} (xs : Fin k → PrebananaFiveAryCylinderLimitCarrier) :
    ∃ A : PrebananaFiniteBooleanModel,
      ∃ e : PrebananaFiniteToCountableEmbedding
        A prebananaCylinderCountableModel,
      ∃ ys : Fin k → A.carrier,
        ∀ i : Fin k, e.hom (ys i) = xs i := by
  classical
  obtain ⟨S, hfinite, hmem⟩ :=
    prebananaFiveAryCylinder_finiteAmbient xs
  letI : Finite S := hfinite
  letI : Fintype S := Fintype.ofFinite S
  let A : PrebananaFiniteBooleanModel :=
    prebananaCylinder_finiteSubmodel S
  let e : PrebananaFiniteToCountableEmbedding
      A prebananaCylinderCountableModel :=
    prebananaCylinder_finiteSubmodel_embedding S
  let ys : Fin k → A.carrier :=
    fun i => ⟨xs i, hmem i⟩
  refine ⟨A, e, ys, ?_⟩
  intro i
  rfl

end SuccessorTree.NonPrecompact
