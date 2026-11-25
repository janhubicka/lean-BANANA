import BANANA.NonPrecompact.FirstOrderFiniteExtension
import Mathlib.Data.Nat.Pairing

/-!
# Fraïssé existence for finite structures

A countable list of embedding requests is serviced repeatedly along a chain of
finite structures. Natural-number labels let a request refer to its base
embedding in every stage containing that base. The limit and the final
back-and-forth argument use mathlib.
-/

namespace SuccessorTree.NonPrecompact

open CategoryTheory FirstOrder Set
open scoped FirstOrder

universe u v w

namespace FiniteFraisse

variable {L : Language.{u, v}} {K : Set (Bundled.{w} L.Structure)}

/-- A finite structure in the class with distinct natural-number labels. -/
private structure Labelled (K : Set (Bundled.{w} L.Structure)) where
  model : Bundled.{w} L.Structure
  mem : model ∈ K
  label : model → ℕ
  injective_label : Function.Injective label

private theorem exists_extend_labels
    {M N : Bundled.{w} L.Structure} [Finite M] [Finite N]
    (f : M ↪[L] N) {labels : M → ℕ} (hinj : Function.Injective labels) :
    ∃ newLabels : N → ℕ, Function.Injective newLabels ∧ ∀ x, newLabels (f x) = labels x := by
  classical
  let : Fintype M := Fintype.ofFinite M
  let : Encodable N := Encodable.ofCountable N
  let bound := (Finset.univ.image labels).sup id
  have le_bound (x : M) : labels x ≤ bound :=
    Finset.le_sup (f := id) (Finset.mem_image_of_mem labels (Finset.mem_univ x))
  let newLabels (x : N) :=
    if hx : x ∈ Set.range f then labels hx.choose else bound + 1 + Encodable.encode x
  refine ⟨newLabels, ?_, ?_⟩
  · intro x y hxy
    dsimp only [newLabels] at hxy
    split at hxy
    next hx =>
      split at hxy
      next hy =>
        rw [← hx.choose_spec, ← hy.choose_spec, hinj hxy]
      next _ =>
        have := le_bound hx.choose
        omega
    next _ =>
      split at hxy
      next hy =>
        have := le_bound hy.choose
        omega
      next _ =>
        apply Encodable.encode_injective
        omega
  · intro x
    have h : f x ∈ Set.range f := ⟨x, rfl⟩
    dsimp only [newLabels]
    rw [dite_eq_left h, f.injective h.choose_spec]

variable (R : ℕ → Bundled.{w} L.Structure)

/-- A request to extend the map given by its natural-number labels along an embedding. -/
private structure Request where
  source : ℕ
  target : ℕ
  embedding : R source ↪[L] R target
  baseLabels : R source → ℕ

private instance [∀ i, Finite (R i)] : Countable (Request R) := by
  let (i : ℕ) : Language.Structure.FG L (R i) := Language.Structure.FG.of_finite
  let code (q : Request R) : Σ i j : ℕ, (R i ↪[L] R j) × (R i → ℕ) :=
    ⟨q.source, q.target, q.embedding, q.baseLabels⟩
  refine Function.Embedding.countable ⟨code, ?_⟩
  rintro ⟨i, j, e, labels⟩ ⟨i', j', e', labels'⟩ h
  dsimp [code] at h
  cases h
  rfl

private abbrev Step (M : Labelled K) :=
  Σ N : Labelled K, {f : M.model ↪[L] N.model // ∀ x, N.label (f x) = M.label x}

private noncomputable def idleStep (M : Labelled K) : Step M :=
  ⟨M, ⟨Language.Embedding.refl L M.model, fun _ => rfl⟩⟩

private noncomputable def activeStep
    (hK : Language.IsFraisse K) (finiteK : ∀ M ∈ K, Finite M)
    (memR : ∀ i, R i ∈ K) (M : Labelled K) (q : Request R)
    (e : R q.source ↪[L] M.model) :
    {s : Step M // ∃ g : R q.target ↪[L] s.1.model,
      g.comp q.embedding = s.2.1.comp e} := by
  classical
  choose N f g hN comm using
    hK.amalgamation (R q.source) M.model (R q.target) e q.embedding (memR _) M.mem (memR _)
  letI := finiteK _ M.mem
  letI := finiteK _ hN
  choose labels hinj hlabels using exists_extend_labels f M.injective_label
  exact ⟨⟨⟨N, hN, labels, hinj⟩, ⟨f, hlabels⟩⟩, g, comm.symm⟩

private noncomputable def answer
    (hK : Language.IsFraisse K) (finiteK : ∀ M ∈ K, Finite M)
    (memR : ∀ i, R i ∈ K) (M : Labelled K) (q : Request R) : Step M := by
  classical
  exact if h : ∃ e : R q.source ↪[L] M.model, ∀ x, M.label (e x) = q.baseLabels x
    then (activeStep R hK finiteK memR M q h.choose).1
    else idleStep M

private theorem answer_extends
    (hK : Language.IsFraisse K) (finiteK : ∀ M ∈ K, Finite M)
    (memR : ∀ i, R i ∈ K) (M : Labelled K) (q : Request R)
    (e : R q.source ↪[L] M.model) (he : ∀ x, M.label (e x) = q.baseLabels x) :
    ∃ g : R q.target ↪[L] (answer R hK finiteK memR M q).1.model,
      g.comp q.embedding = (answer R hK finiteK memR M q).2.1.comp e := by
  classical
  let h : ∃ e : R q.source ↪[L] M.model, ∀ x, M.label (e x) = q.baseLabels x := ⟨e, he⟩
  have eq : h.choose = e := by
    ext x
    exact M.injective_label ((h.choose_spec x).trans (he x).symm)
  unfold answer
  rw [dite_eq_left h]
  rw [← eq]
  exact (activeStep R hK finiteK memR M q h.choose).2

variable [∀ i, Finite (R i)]

@[instance_reducible]
private noncomputable def requestEncoding : Encodable (Request R) := Encodable.ofCountable _

private noncomputable def initial (memR : ∀ i, R i ∈ K) : Labelled K :=
  letI : Encodable (R 0) := Encodable.ofCountable _
  ⟨R 0, memR 0, Encodable.encode, Encodable.encode_injective⟩

private noncomputable def next
    (hK : Language.IsFraisse K) (finiteK : ∀ M ∈ K, Finite M)
    (memR : ∀ i, R i ∈ K) (n : ℕ) (M : Labelled K) : Step M :=
  letI := requestEncoding R
  match Encodable.decode (α := Request R) n.unpair.1 with
  | none => idleStep M
  | some q => answer R hK finiteK memR M q

variable (hK : Language.IsFraisse K) (finiteK : ∀ M ∈ K, Finite M) (memR : ∀ i, R i ∈ K)

private noncomputable def stage : ℕ → Labelled K
  | 0 => initial R memR
  | n + 1 => (next R hK finiteK memR n (stage n)).1

private noncomputable abbrev G (n : ℕ) : Type w :=
  (stage R hK finiteK memR n).model

private noncomputable instance stageStructure (n : ℕ) : L.Structure (G R hK finiteK memR n) :=
  (stage R hK finiteK memR n).model.str

private noncomputable def stepMap (n : ℕ) :
    G R hK finiteK memR n ↪[L] G R hK finiteK memR (n + 1) :=
  (next R hK finiteK memR n (stage R hK finiteK memR n)).2.1

private noncomputable abbrev maps (i j : ℕ) (h : i ≤ j) :
    G R hK finiteK memR i ↪[L] G R hK finiteK memR j :=
  Language.DirectedSystem.natLERec (stepMap R hK finiteK memR) i j h

private theorem maps_label (i j : ℕ) (h : i ≤ j) (x : G R hK finiteK memR i) :
    (stage R hK finiteK memR j).label (maps R hK finiteK memR i j h x) =
      (stage R hK finiteK memR i).label x := by
  induction h with
  | refl => simp [maps, Language.DirectedSystem.natLERec, Nat.leRecOn_self]
  | @step j h ih =>
    change (stage R hK finiteK memR (j + 1)).label
      (Language.DirectedSystem.natLERec (stepMap R hK finiteK memR) i (j + 1)
        (Nat.le.step h) x) = _
    rw [Language.DirectedSystem.natLERec, Nat.leRecOn_succ h, ← Language.DirectedSystem.natLERec]
    exact ((next R hK finiteK memR j (stage R hK finiteK memR j)).2.2 _).trans ih

private noncomputable abbrev Limit :=
  Language.DirectLimit (G R hK finiteK memR) (maps R hK finiteK memR)

private noncomputable abbrev incl (n : ℕ) : G R hK finiteK memR n ↪[L] Limit R hK finiteK memR :=
  Language.DirectLimit.of L ℕ (G R hK finiteK memR) (maps R hK finiteK memR) n

private theorem factor
    {A : Bundled.{w} L.Structure} [Finite A] (f : A ↪[L] Limit R hK finiteK memR) :
    ∃ (n : ℕ) (e : A ↪[L] G R hK finiteK memR n),
      (incl R hK finiteK memR n).comp e = f := by
  obtain ⟨n, g, hg⟩ := Language.DirectLimit.exists_quotient_mk'_sigma_mk'_eq
    (G R hK finiteK memR) (maps R hK finiteK memR) (fun x => f x)
  let i := incl R hK finiteK memR n
  let f' := f.codRestrict i.toHom.range (fun x => ⟨g x, (congrFun hg x).symm⟩)
  refine ⟨n, i.equivRange.symm.toEmbedding.comp f', ?_⟩
  ext x
  change (i.toHom.range.subtype (i.equivRange (i.equivRange.symm (f' x)))) = f x
  rw [Language.Equiv.apply_symm_apply]
  rfl

private theorem step_serves
    (n : ℕ) (q : Request R)
    (hcode : letI := requestEncoding R; Encodable.decode (α := Request R) n.unpair.1 = some q)
    (e : R q.source ↪[L] G R hK finiteK memR n)
    (he : ∀ x, (stage R hK finiteK memR n).label (e x) = q.baseLabels x) :
    ∃ g : R q.target ↪[L] G R hK finiteK memR (n + 1),
      g.comp q.embedding = (stepMap R hK finiteK memR n).comp e := by
  change ∃ g : R q.target ↪[L]
      (next R hK finiteK memR n (stage R hK finiteK memR n)).1.model,
    g.comp q.embedding = (next R hK finiteK memR n (stage R hK finiteK memR n)).2.1.comp e
  unfold next
  rw [hcode]
  exact answer_extends R hK finiteK memR _ _ e he

private theorem representative_extension
    (a b : ℕ) (f : R a ↪[L] R b) (e : R a ↪[L] Limit R hK finiteK memR) :
    ∃ g : R b ↪[L] Limit R hK finiteK memR, g.comp f = e := by
  let := requestEncoding R
  obtain ⟨i, e', he'⟩ := factor R hK finiteK memR e
  let q : Request R := ⟨a, b, f, fun x => (stage R hK finiteK memR i).label (e' x)⟩
  let n := Nat.pair (Encodable.encode q) i
  have hin : i ≤ n := Nat.right_le_pair _ _
  let en := (maps R hK finiteK memR i n hin).comp e'
  have hen : ∀ x, (stage R hK finiteK memR n).label (en x) = q.baseLabels x :=
    fun x => maps_label R hK finiteK memR i n hin (e' x)
  have hcode : Encodable.decode (α := Request R) n.unpair.1 = some q := by
    simp only [n, Nat.unpair_pair, Encodable.encodek]
  obtain ⟨g, hg⟩ := step_serves R hK finiteK memR n q hcode en hen
  refine ⟨(incl R hK finiteK memR (n + 1)).comp g, ?_⟩
  ext x
  change incl R hK finiteK memR (n + 1) (g (f x)) = e x
  have hx : g (f x) = stepMap R hK finiteK memR n (en x) :=
    DFunLike.congr_fun hg x
  rw [hx]
  have hs : stepMap R hK finiteK memR n (en x) =
      maps R hK finiteK memR n (n + 1) (Nat.le_succ n) (en x) := by
    simp [maps, Language.DirectedSystem.natLERec, Nat.leRecOn_succ (Nat.le_refl n),
      Nat.leRecOn_self]
  rw [hs]
  rw [show incl R hK finiteK memR (n + 1)
      (maps R hK finiteK memR n (n + 1) (Nat.le_succ n) (en x)) =
      incl R hK finiteK memR n (en x) from Language.DirectLimit.of_f]
  exact (Language.DirectLimit.of_f (hij := hin)).trans (DFunLike.congr_fun he' x)

private theorem extension
    (covers : ∀ A ∈ K, ∃ a, Nonempty (R a ≃[L] A))
    {A B : Bundled.{w} L.Structure} (hA : A ∈ K) (hB : B ∈ K)
    (i : A ↪[L] B) (f : A ↪[L] Limit R hK finiteK memR) :
    ∃ g : B ↪[L] Limit R hK finiteK memR, g.comp i = f := by
  obtain ⟨a, ⟨eA⟩⟩ := covers A hA
  obtain ⟨b, ⟨eB⟩⟩ := covers B hB
  let i' := (eB.symm.toEmbedding.comp i).comp eA.toEmbedding
  let f' := f.comp eA.toEmbedding
  obtain ⟨g, hg⟩ := representative_extension R hK finiteK memR a b i' f'
  refine ⟨g.comp eB.symm.toEmbedding, ?_⟩
  ext x
  have hx := DFunLike.congr_fun hg (eA.symm x)
  simpa [i', f'] using hx

private theorem age_eq
    (covers : ∀ A ∈ K, ∃ a, Nonempty (R a ≃[L] A)) :
    L.age (Limit R hK finiteK memR) = K := by
  apply subset_antisymm
  · rw [Language.age_directLimit _ (maps R hK finiteK memR)]
    exact iUnion_subset (fun n => hK.hereditary _ (stage R hK finiteK memR n).mem)
  · intro A hA
    let B := (stage R hK finiteK memR 0).model
    have hB : B ∈ K := (stage R hK finiteK memR 0).mem
    obtain ⟨T, hT, ⟨i⟩, ⟨j⟩⟩ := hK.jointEmbedding B hB A hA
    obtain ⟨g, _⟩ := extension R hK finiteK memR covers hB hT i (incl R hK finiteK memR 0)
    exact ⟨hK.FG A hA, ⟨g.comp j⟩⟩

include hK finiteK memR in
private theorem exists_limit_of_representatives [Countable (Σ l, L.Functions l)]
    (covers : ∀ A ∈ K, ∃ a, Nonempty (R a ≃[L] A)) :
    ∃ (M : Bundled.{w} L.Structure) (_ : Countable M), Language.IsFraisseLimit K M := by
  let M := Limit R hK finiteK memR
  have cg : Language.Structure.CG L M :=
    Language.DirectLimit.cg (maps R hK finiteK memR)
      (fun n => (hK.FG _ (stage R hK finiteK memR n).mem).cg)
  let : Countable M := Language.Structure.cg_iff_countable.mp cg
  have hAge : L.age M = K := age_eq R hK finiteK memR covers
  have substructure_mem (S : L.Substructure M) (hS : S.FG) :
      (⟨S, inferInstance⟩ : Bundled L.Structure) ∈ K := by
    have h := Language.age.fg_substructure hS
    rw [hAge] at h
    exact h
  have finite_fg (S : L.Substructure M) (hS : S.FG) : Finite S :=
    finiteK ⟨S, inferInstance⟩ (substructure_mem S hS)
  let model : Bundled.{w} L.Structure := ⟨M, inferInstance⟩
  refine ⟨model, (inferInstance : Countable M), ⟨?_, hAge⟩⟩
  refine isUltrahomogeneous_of_finite_extension finite_fg ?_
  intro S T hST hS hT f
  have hSK := substructure_mem S Language.Substructure.FG.of_finite
  have hTK := substructure_mem T Language.Substructure.FG.of_finite
  exact extension R hK finiteK memR covers hSK hTK (Language.Substructure.inclusion hST) f

end FiniteFraisse

/-- A Fraïssé class of finite structures in a language with countably many
function symbols has a countable Fraïssé limit. -/
theorem exists_finiteFraisseLimit
    {L : Language.{u, v}} {K : Set (Bundled.{w} L.Structure)}
    [Countable (Σ l, L.Functions l)]
    (hK : Language.IsFraisse K) (finiteK : ∀ A ∈ K, Finite A) :
    ∃ (M : Bundled.{w} L.Structure) (_ : Countable M), Language.IsFraisseLimit K M := by
  classical
  obtain ⟨F, hF⟩ := hK.is_essentially_countable.exists_eq_range (hK.is_nonempty.image _)
  have liftRep (n : ℕ) : ∃ A ∈ K, Quotient.mk' A = F n :=
    (show F n ∈ Quotient.mk' '' K from hF.symm ▸ mem_range_self n)
  choose R memR rep using liftRep
  let (n : ℕ) : Finite (R n) := finiteK (R n) (memR n)
  refine FiniteFraisse.exists_limit_of_representatives R hK finiteK memR ?_
  intro A hA
  obtain ⟨n, hn⟩ := (show Quotient.mk' A ∈ range F from hF ▸ mem_image_of_mem _ hA)
  exact ⟨n, Quotient.exact ((rep n).trans hn)⟩

end SuccessorTree.NonPrecompact
